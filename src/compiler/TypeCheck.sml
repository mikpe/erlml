(*
 * Copyright 2017-2018 Mikael Pettersson
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)
structure TypeCheck : TYPE_CHECK =
  struct

    exception TypeCheck

    fun sayErr s = TextIO.output(TextIO.stdErr, s)

    fun nyi msg =
      (sayErr("TypeCheck: nyi " ^ msg ^ "\n"); raise TypeCheck)

    fun error msg =
      (sayErr("TypeCheck: " ^ msg ^ "\n"); raise TypeCheck)

    fun labelToString(Basis.IDlab id) = id
      | labelToString(Basis.INTlab i) = Int.toString i

    (*
     * IDENTIFIERS
     *)

    fun readBasisFile(id, ext) =
      (* TODO: path for basis files? *)
      SOME(Basis.read(id ^ ext ^ ".basis")) handle _ => NONE

    fun longIdToString'(strids, id) = String.concatWith "." (strids @ [id])
    fun longIdToString(Absyn.LONGID(strids, id)) = longIdToString'(strids, id)

    fun unbound(kind, strids, id) =
      error("unbound " ^ kind ^ " " ^ longIdToString'(strids, id))
    fun unboundVid(strids, vid) = unbound("vid", strids, vid)
    fun unboundStrId(strids, strid) = unbound("strid", strids, strid)
    fun unboundTyCon(strids, tycon) = unbound("tycon", strids, tycon)
    fun unboundTyVar tyvar = unbound("tyvar", [], tyvar)
    fun unboundSigId sigid = unbound("sigid", [], sigid)
    fun lookupSigId'(Basis.BASIS(Basis.G dict, _), sigid) =
      Dict.find(dict, sigid)

    fun lookupSigId(B, sigid) =
      case lookupSigId'(B, sigid)
       of SOME sigma => sigma
	| NONE =>
	  case lookupSigId'(Basis.initialBasis, sigid)
	   of SOME sigma => sigma
	    | NONE =>
	      case readBasisFile(sigid, ".sig")
	       of NONE => unboundSigId sigid
		| SOME B' =>
		  case lookupSigId'(B', sigid)
		   of SOME sigma => sigma
		    | NONE => unboundSigId sigid

    fun gBindSigId(Basis.G dict, sigid, sigma) =
      case Dict.find(dict, sigid)
       of NONE => Basis.G(Dict.insert(dict, sigid, sigma))
	| SOME _ => error("sigid " ^ sigid ^ " already bound")

    fun bPlusG(Basis.BASIS(Basis.G dict1, E), Basis.G dict2) =
      Basis.BASIS(Basis.G(Dict.plus(dict1, dict2)), E)

    fun lookupFirstStrId(Basis.E(Basis.SE dict, _, _), strid) =
      case Dict.find(dict, strid)
       of SOME env => env
	| NONE =>
	  let val Basis.BASIS(_, Basis.E(Basis.SE dict, _, _)) = Basis.initialBasis
	  in
	    case Dict.find(dict, strid)
	     of SOME env => env
	      | NONE =>
		case readBasisFile(strid, ".sml")
		 of NONE => unboundStrId([], strid)
		  | SOME(Basis.BASIS(_, Basis.E(Basis.SE dict, _, _))) =>
		    case Dict.find(dict, strid)
		     of SOME env => env
		      | NONE => unboundStrId([], strid)
	  end

    fun lookupNextStrId(strid, (Basis.E(Basis.SE dict, _, _), revpfx)) =
      case Dict.find(dict, strid)
       of SOME env => (env, strid :: revpfx)
	| NONE => unboundStrId(List.rev revpfx, strid)

    (* For a short VId we look it up first in the current Env, and then in toplevelValEnv.
       For a long VId, we look up the first StrId first in the current Env, then in the
       initial Basis, and lastly from a .basis file.  The resulting Env is then used to
       look up subsequent StrIds and finally the VId. *)

    fun lookupVid(Basis.E(_, _, Basis.VE dict), vid) =
      case Dict.find(dict, vid)
       of NONE =>
          (case Dict.find(Basis.toplevelValEnv, vid)
	    of NONE => NONE
	     | SOME(longvid, sigma, idstatus) => SOME(SOME longvid, sigma, idstatus))
	| SOME(sigma, idstatus) => SOME(NONE, sigma, idstatus)

    fun lookupLongVid(env, Absyn.LONGID([], vid)) =
        (case lookupVid(env, vid)
	  of SOME(longVidOpt, sigma, idstatus) => (longVidOpt, sigma, idstatus)
	   | NONE => unboundVid([], vid))
      | lookupLongVid(env, Absyn.LONGID(strid :: strids, vid)) =
	let val env = lookupFirstStrId(env, strid)
	    val (Basis.E(_, _, Basis.VE dict), revpfx) = List.foldl lookupNextStrId (env, [strid]) strids
	in
          case Dict.find(dict, vid)
	   of SOME(sigma, idstatus) => (NONE, sigma, idstatus)
	    | NONE => unboundVid(List.rev revpfx, vid)
	end

    fun veBindVid(Basis.VE dict, vid, sigma, idstatus) = (* VE+{vid->idstatus}, but checks vid not in Dom(VE) *)
      case Dict.find(dict, vid)
       of NONE => Basis.VE(Dict.insert(dict, vid, (sigma, idstatus)))
	| SOME _ => error("vid " ^ vid ^ " already bound")

    fun vePlusVE(VE, Basis.VE VE') = (* VE+VE', but checks Dom(VE) and Dom(VE') are disjoint *)
      let fun bind(vid, (sigma, idstatus), VE) = veBindVid(VE, vid, sigma, idstatus)
      in
	Dict.fold(bind, VE, VE')
      end

    fun cPlusVE(Basis.E(SE, TE, Basis.VE dict1), Basis.VE dict2) =
      Basis.E(SE, TE, Basis.VE(Dict.plus(dict1, dict2)))

    val ePlusVE = cPlusVE

    fun cPlusE(Basis.E(Basis.SE SE1, Basis.TE TE1, Basis.VE VE1), Basis.E(Basis.SE SE2, Basis.TE TE2, Basis.VE VE2)) =
      Basis.E(Basis.SE(Dict.plus(SE1, SE2)), Basis.TE(Dict.plus(TE1, TE2)), Basis.VE(Dict.plus(VE1, VE2)))

    val ePlusE = cPlusE

    fun seBindStrId(Basis.SE dict, strid, E) = (* SE+{strid->E}, but checks strid not in Dom(SE) *)
      case Dict.find(dict, strid)
       of NONE => Basis.SE(Dict.insert(dict, strid, E))
	| SOME _ => error("strid " ^ strid ^ " already bound")

    fun sePlusSE(SE, Basis.SE SE') = (* SE+SE' *)
      let fun bind(strid, E, SE) = seBindStrId(SE, strid, E)
      in
	Dict.fold(bind, SE, SE')
      end

    fun ePlusSE(Basis.E(SE1, TE, VE), SE2) = (* E+SE *)
      Basis.E(sePlusSE(SE1, SE2), TE, VE)

    fun teBindTyCon(Basis.TE dict, tycon, tyfcn, VE) = (* TE+{tycon->(tyfcn,VE)}, but checks tycon not in Dom(TE) *)
      case Dict.find(dict, tycon)
       of NONE => Basis.TE(Dict.insert(dict, tycon, Basis.TYSTR(tyfcn, VE)))
	| SOME _ => error("tycon " ^ tycon ^ " already bound")

    fun tePlusTE(TE, Basis.TE TE') = (* TE+TE', but checks Dom(TE) and Dom(TE') are disjoint *)
      let fun bind(tycon, Basis.TYSTR(tyfcn, VE), TE) = teBindTyCon(TE, tycon, tyfcn, VE)
      in
	Dict.fold(bind, TE, TE')
      end

    fun ePlusTE(Basis.E(SE, Basis.TE dict1, VE), Basis.TE dict2) =
      Basis.E(SE, Basis.TE(Dict.plus(dict1, dict2)), VE)

    val cPlusTE = ePlusTE

    (*
     * TYPE EXPRESSIONS
     *)

    fun lookupLongTyCon(Basis.E(_, Basis.TE dict, _), Absyn.LONGID([], tycon)) =
	  (case Dict.find(dict, tycon)
	     of SOME tystr => tystr
	      | NONE =>
		  case Dict.find(Basis.toplevelTyEnv, tycon)
		    of SOME tystr => tystr
		     | NONE => unboundTyCon([], tycon))
      | lookupLongTyCon(env, Absyn.LONGID(strid :: strids, tycon)) =
	  let val env = lookupFirstStrId(env, strid)
	      val (Basis.E(_, Basis.TE dict, _), revpfx) = List.foldl lookupNextStrId (env, [strid]) strids
	  in
	    case Dict.find(dict, tycon)
	      of SOME tystr => tystr
	       | NONE => unboundTyCon(List.rev revpfx, tycon)
	  end

    fun checkRho rho = (* PRE: rho is sorted *)
      let fun loop(_, []) = ()
	    | loop(l1, (l2, _) :: rest) =
	        if l1 <> l2 then loop(l2, rest)
		else error("label " ^ labelToString l2 ^ " already bound")
      in
	case rho
	  of [] => ()
	   | (l1, _) :: rest => loop(l1, rest)
      end

    fun funTy(dom, ran) = Types.CONS([dom, ran], Basis.funTyname)

    fun elabTy(C, ty) = (* C |- ty => tau *)
      case ty
       of Absyn.VARty tyvar => Types.VAR(Types.RIGID tyvar)
	| Absyn.RECty tyrow => elabTyRow(C, tyrow)
	| Absyn.CONSty(tyseq, longtycon) => elabConsTy(C, tyseq, longtycon)
	| Absyn.FUNty(ty, ty') => funTy(elabTy(C, ty), elabTy(C, ty'))

    and elabTyRow(C, tyrow) =
      let fun elabField(label, ty) = (label, elabTy(C, ty))
	  val rho = Types.sortFields(List.map elabField tyrow)
	  val _ = checkRho rho
      in
	Types.REC(Types.mkRecord(rho, false))
      end

    and elabConsTy(C, tyseq, longtycon) =
      let val taus = List.map (fn ty => elabTy(C, ty)) tyseq
	  val Basis.TYSTR(tyfcn, _) = lookupLongTyCon(C, longtycon)
      in
	Types.applyTyfcn(tyfcn, taus)
      end

    (*
     * Special Constants
     *)

    fun sconType scon = (* type(scon) *)
      case scon
       of Absyn.INTsc _ => Basis.intTy
	| Absyn.WORDsc _ => Basis.wordTy
	| Absyn.REALsc _ => Basis.realTy
	| Absyn.STRINGsc _ => Basis.stringTy
	| Absyn.CHARsc _ => Basis.charTy

    (*
     * Patterns
     *)

    fun elabPat(C, level, gen, VE, pat) = (* C |- pat => (VE,tau) *)
      case pat
       of Absyn.WILDpat => (* 32 *)
	  let val tau = Types.VAR(Types.mkFreeTyvar level)
	  in
	    (VE, tau)
	  end
	| Absyn.SCONpat scon => (VE, sconType scon) (* 33 *)
	| Absyn.VIDpat(longvid, refOptIdStatus) => (* (34) or (35) *)
	  let fun v vid = (* 34 *)
		let val tau = Types.VAR(Types.mkFreeTyvar level)
		    val sigma = gen tau
		    val _ = refOptIdStatus := SOME Basis.VAL
		in
		  (veBindVid(VE, vid, sigma, Basis.VAL), tau)
		end
	      fun cOrE(sigma, is) = (* 35 *)
		let val _ = refOptIdStatus := SOME is
		    val (_, tau) = Types.instFree(sigma, level)
		in
		  (VE, tau)
		end
	  in
	    case longvid
	     of Absyn.LONGID([], vid) =>
		(case lookupVid(C, vid)
		  of NONE => v vid
		   | SOME(_, _, Basis.VAL) => v vid
		   | SOME(_, sigma, is as Basis.CON _) => cOrE(sigma, is)
		   | SOME(_, sigma, is as Basis.EXN _) => cOrE(sigma, is))
	     | _ =>
	       let val (_, sigma, is) = lookupLongVid(C, longvid)
		   val _ = case is
			    of Basis.VAL => error("longvid " ^ longIdToString longvid ^ " in pattern is a variable")
			     | _ => ()
	       in
		 cOrE(sigma, is)
	       end
	  end
	| Absyn.RECpat(patrow, flexP) =>
	  let val (VE, rho) = elabPatrow(C, level, gen, VE, patrow, flexP)
	  in
	    (VE, Types.REC rho)
	  end
	| Absyn.CONSpat(longvid, pat) =>
	  let val (_, sigma, is) = lookupLongVid(C, longvid)
	      val _ = case is
		       of Basis.VAL => error("longvid " ^ longIdToString longvid ^ " in pattern is a variable")
			| _ => ()
	      val (VE, tau') = elabPat(C, level, gen, VE, pat)
	      val tau = Types.VAR(Types.mkFreeTyvar level)
	      val (_, tau'') = Types.instFree(sigma, level)
	      val _ = Unify.unify(tau'', funTy(tau', tau))
	  in
	    (VE, tau)
	  end
	| Absyn.TYPEDpat(pat, ty) =>
	  let val (VE, tau) = elabPat(C, level, gen, VE, pat)
	      val tau' = elabTy(C, ty)
	      val _ = Unify.unify(tau, tau')
	  in
	    (VE, tau)
	  end
	| Absyn.ASpat(vid, pat) =>
	  let val _ = case lookupVid(C, vid)
		       of NONE => ()
			| SOME(_, _, Basis.VAL) => ()
			| SOME(_, _, _) => error("vid " ^ vid ^ " is a constructor")
	      val (VE, tau) = elabPat(C, level, gen, VE, pat)
	      val sigma = gen tau
	  in
	    (veBindVid(VE, vid, sigma, Basis.VAL), tau)
	  end

    and elabPatrow(C, level, gen, VE, patrow, flexP) = (* C |- patrow => (VE,rho) *)
      let val (VE, rho) = List.foldl (elabPatrowField C level gen) (VE, []) patrow
	  val rho = Types.sortFields rho
	  val _ = checkRho rho
      in
	(VE, Types.mkRecord(rho, flexP))
      end

    and elabPatrowField C level gen ((label, pat), (VE, rho)) =
      let val (VE, tau) = elabPat(C, level, gen, VE, pat)
      in
	(VE, (label, tau) :: rho)
      end

    (*
     * Type Bindings
     *
     * There appears to be some confusion regarding the scope of explicit type variables in
     * typbind and datbind declarations.  SML'90 had a syntactic restriction 2.9, third bullet,
     * "Any tyvar occurring within the right side must occur in tyvarseq".  Furthermore, in 4.4
     * it specified that type functions must be closed.  Both of these restrictions are removed
     * in SML'97.  However, Rossberg's "Defects" document lists this as an error in SML'97, and
     * both Hamlet and MoscowML enforce the SML'90 rule.  We do the same.
     *)

    fun checkFreeTyVars(tyvarseq, ty) =
      let fun checkTy ty =
	    case ty
	      of Absyn.VARty tyvar => if Util.member(tyvar, tyvarseq) then () else unboundTyVar tyvar
	       | Absyn.RECty tyrow => List.app checkField tyrow
	       | Absyn.CONSty(tyseq, _) => List.app checkTy tyseq
	       | Absyn.FUNty(ty1, ty2) => (checkTy ty1; checkTy ty2)
	  and checkField(_, ty) = checkTy ty
      in
	checkTy ty
      end

    (* Map list of syntactic tyvars to semantic tyvars.
     * Check syntactic retrictions (no tyvarseq may contain the same tyvar twice).
     *)
    fun elabTyvarseq tyvarseq =
      let fun loop([], acc) = List.rev acc
	    | loop(tyvar :: tyvarseq, acc) =
		if Util.member(tyvar, tyvarseq) then error("tyvar '" ^ tyvar ^ " already bound")
		else loop(tyvarseq, (Types.RIGID tyvar) :: acc)
      in
	loop(tyvarseq, [])
      end

    fun elabTypBind' C ((tyvarseq, tycon, ty), TE) =
      let val _ = checkFreeTyVars(tyvarseq, ty)
	  val alphas = elabTyvarseq tyvarseq
	  val tau = elabTy(C, ty)
	  val tyfcn = Types.lambda(alphas, tau)
      in
	teBindTyCon(TE, tycon, tyfcn, Basis.emptyVE)
      end

    fun elabTypBind(C, Absyn.TYPBIND typbinds) = (* C |- typbind => TE *)
      List.foldl (elabTypBind' C) Basis.emptyTE typbinds

    (*
     * Datatype Bindings
     *)

    fun checkConbindFreeTyVars tyvarseq (_, tyOpt) =
      case tyOpt
        of NONE => ()
	 | SOME ty => checkFreeTyVars(tyvarseq, ty)

    fun checkConbindsFreeTyVars(tyvarseq, Absyn.CONBIND conbinds) =
      List.app (checkConbindFreeTyVars tyvarseq) conbinds

    fun elabDatbindSkeletal'((tyvarseq, tycon, conbinds), (TE, datbind')) =
      let val _ = checkConbindsFreeTyVars(tyvarseq, conbinds)
	  val alphas = elabTyvarseq tyvarseq
	  val tyname = Types.TYNAME{strid = "FIXME", tycon = tycon, eq = ref Types.MAYBE}
	  val tau = Types.CONS(List.map Types.VAR alphas, tyname)
	  val tyfcn = Types.lambda(alphas, tau)
      in
	(teBindTyCon(TE, tycon, tyfcn, Basis.emptyVE), (tyname, tau, tyfcn, (tyvarseq, tycon, conbinds)) :: datbind')
      end

    (* Elaborate datbind to skeletal TE (with empty VEs) and datbind annotated with tynames, taus, and tyfcns.
     * Check each datbind's tyvarseq for duplicates.
     * Check each conbind for free tyvars wrt its tyvarseq.
     * Create fresh tynames, initially admitting equality.
     * Annotate each datbind with its tyname.
     * Return skeletal TE and list of annotated datbinds.
     *)
    fun elabDatbindSkeletal(Absyn.DATBIND datbinds) = (* |- datbind => TE_skel,datbind' *)
      List.foldl elabDatbindSkeletal' (Basis.emptyTE, []) datbinds

    fun checkWithtype' (Basis.TE dict) (_, tycon, _) =
      case Dict.find(dict, tycon)
	of NONE => ()
	 | SOME _ => error("tycon " ^ tycon ^ " already bound")

    (* Check that a withtype does not redefine a tycon defined in the datbind.  *)
    fun checkWithtype(TE_skel, Absyn.TYPBIND typbinds) =
      List.app (checkWithtype' TE_skel) typbinds

    (* 2.9 Syntactic Restrictions, 5th bullet:
     * ``No datbind, valbind, or exbind may bind "true", "false", "nil", "::" or "ref".
     *   No datbind or exbind may bind "it".''
     * 3.5 imposes the same restrictions on datdesc, valdesc, and exdesc.
     *)
    fun allowedVid vid = (* val(bind | desc) *)
      case vid
       of "true" => false
	| "false" => false
	| "nil" => false
	| "::" => false
	| "ref" => false
	| _ => true

    fun allowedCon vid = (* (dat | ex)(bind | desc) *)
      case vid
       of "it" => false
	| _ => allowedVid vid

    fun veBindCon(VE, vid, sigma, is) =
      let val _ = if allowedCon vid then ()
		  else error("invalid binding of " ^ vid)
      in
	veBindVid(VE, vid, sigma, is)
      end

    fun elabConbind' C tau ((vid, tyOpt), (VE, taus)) =
      case tyOpt
       of NONE =>
	  (* Strictly speaking this genAll should be a genNone (29), followed by
	     a dummy instantiation and a genAll in elabDatbind'' (28).  Doing a
	     genAll here is simpler and has the same effect.  *)
	  let val sigma = Types.genAll tau
	  in
	    (veBindCon(VE, vid, sigma, Basis.CON false), taus)
	  end
	| SOME ty =>
	  let val tau' = elabTy(C, ty)
	      val sigma = Types.genAll(funTy(tau', tau))
	  in
	    (veBindCon(VE, vid, sigma, Basis.CON true), tau' :: taus)
	  end

    fun elabConbind(C, tau, Absyn.CONBIND conbinds) = (* C,tau |- conbind => VE,tau* *)
      List.foldl (elabConbind' C tau) (Basis.emptyVE, []) conbinds

    fun elabDatbind'' C ((tyname, tau, tyfcn, (tyvarseq, tycon, conbind)), (VE, TE, datbind'')) =
      let val (VE', VEtaus) = elabConbind(C, tau, conbind)
      in
	(vePlusVE(VE, VE'), teBindTyCon(TE, tycon, tyfcn, VE'), (tyname, VEtaus) :: datbind'')
      end

    fun elabDatbind'(C, datbind') = (* C |- datbind' => (VE,TE,datbind'') *)
      List.foldl (elabDatbind'' C) (Basis.emptyVE, Basis.emptyTE, []) datbind'

    fun veAdmitsEq VEtaus =
      let fun loop([], eq) = eq
	    | loop(tau :: taus, eq) =
		case Types.tyAdmitsEq tau
		  of Types.NEVER => Types.NEVER
		   | Types.MAYBE => loop(taus, Types.MAYBE)
		   | Types.ALWAYS => loop(taus, eq)
      in
	loop(VEtaus, Types.ALWAYS)
      end

    fun maximisesEquality datbind'' = (* (tyname * VEtaus) list -> unit *)
      let fun loop([], false, _) = ()
	    | loop([], true, acc) = loop(acc, false, [])
	    | loop((tyname as Types.TYNAME{eq, ...}, VEtaus) :: rest, restart, acc) =
		case veAdmitsEq VEtaus
		  of Types.ALWAYS =>
		     (eq := Types.ALWAYS;
		      loop(rest, true, acc))
		   | Types.MAYBE =>
		     loop(rest, restart, (tyname, VEtaus) :: acc)
		   | Types.NEVER =>
		     (eq := Types.NEVER;
		      loop(rest, true, acc))
      in
	loop(datbind'', false, [])
      end

    (* 1. Create TE_skel = {tycon -> (tyfcn,VEempty)} for all tycon in datbind.
     *    a) check each tyvarseq for duplicates, and each conbind for free tyvars wrt its tyvarseq
     *    b) create fresh tynames, initially admitting equality
     *    c) create datbind' where each datbind is annotated with its tyname and tyfcn
     * 2. Using TE_skel elaborate withtype to TE_with.
     *    a) check that the withtype does not redefine a tycon from the datbind
     *    b) elaborate the withtype as a normal typbind in C+TE_skel
     * 3. Using TE_skel+TE_with elaborate datbind' to VE and TE_datb.
     *    a) also create datbind'' as a list of pairs of tynames and lists of constructor types
     * 4. For each (tyfcn,VE') in TE_datb, if VE' does not admit equality, clear tyfcn's tyname's eq attribute.
     *    This actually operates on the (tycon, taus) in datbind''.
     *    Iterate until fixpoint.
     * 5. Return VE,TE_datb+TE_with
     *)
    fun elabDatBind(C, datbind, typbind) = (* C |- datbind => VE,TE except we also deal with the withtype *)
      let val (TE_skel, datbind') = elabDatbindSkeletal datbind
	  val _ = checkWithtype(TE_skel, typbind)
	  val TE_with = elabTypBind(cPlusTE(C, TE_skel), typbind)
	  val (VE, TE_datb, datbind'') = elabDatbind'(cPlusTE(cPlusTE(C, TE_skel), TE_with), datbind')
	  val _ = maximisesEquality datbind''
      in
	(VE, tePlusTE(TE_datb, TE_with))
      end

    (*
     * Exception Bindings
     *)

    fun elabExBind' C (exb, VE) =
      case exb
       of Absyn.CONexb vid => veBindCon(VE, vid, Types.genNone Basis.exnTy, Basis.EXN false)
	| Absyn.OFexb(vid, ty) =>
	  (* This genNone is correct, see (20) and its comment.  *)
	  let val tau = elabTy(C, ty)
	      val sigma = Types.genNone(funTy(tau, Basis.exnTy))
	  in
	    veBindCon(VE, vid, sigma, Basis.EXN true)
	  end
	| Absyn.EQexb(vid, longvid) =>
	  case lookupLongVid(C, longvid)
	   of (_, sigma, is as Basis.EXN _) => veBindCon(VE, vid, sigma, is)
	    | _ => error "exception aliasing non-exception"

    fun elabExBind(C, exbind) = (* C |- exbind => VE *)
      List.foldl (elabExBind' C) Basis.emptyVE exbind

    (*
     * 4.7 Non-expansive Expressions
     *)

    fun isConexp(C, exp) =
      case exp
       of Absyn.TYPEDexp(exp, _) => isConexp(C, exp)
	| Absyn.VIDexp(refLongVid, _) =>
	  let val longvid = !refLongVid
	  in
	    case longvid
	     of Absyn.LONGID([], "ref") => false
	      | _ =>
		let val (_, _, is) = lookupLongVid(C, longvid)
		in
		  case is
		   of Basis.CON _ => true
		    | Basis.EXN _ => true
		    | Basis.VAL => false
		end
	  end
	| _ => false

    fun isNexp(C, exp) =
      case exp
       of Absyn.SCONexp _ => true
	| Absyn.VIDexp _ => true
	| Absyn.RECexp exprow => List.all (isNexpField C) exprow
	| Absyn.LETexp _ => false
	| Absyn.APPexp(f, arg) => isConexp(C, f) andalso isNexp(C, arg)
	| Absyn.TYPEDexp(exp, _) => isNexp(C, exp)
	| Absyn.HANDLEexp _ => false
	| Absyn.RAISEexp _ => false
	| Absyn.FNexp _ => true

    and isNexpField C (_, exp) = isNexp(C, exp)

    (*
     * Expressions
     *)

    fun elabValRecPat C level ((pat, match), (VE, recs')) =
      (* FIXME: in this case pat must permit rebinding a vid even if it has "c" is;
	 c.f. the comment to rule (26) *)
      let val (VE, tau) = elabPat(C, level, Types.genNone, VE, pat)
      in
	(VE, (tau, match) :: recs')
      end

    fun checkValVid vid =
      if allowedVid vid then ()
      else error("invalid binding of " ^ vid)

    fun checkValEnvVids(Basis.VE dict) =
      Dict.fold(fn(vid, _, ()) => checkValVid vid, (), dict)

    fun closVE(level, Basis.VE dict) =
      let fun clos(vid, (sigma, is), VE) =
	    let val (_, tau) = Types.instRigid sigma
		val sigma = Types.genLimit(tau, level)
	    in
	      veBindVid(VE, vid, sigma, is)
	    end
      in
	Dict.fold(clos, Basis.emptyVE, dict)
      end

    fun elabExp(C, level, exp) = (* C |- exp => tau *)
      case exp
       of Absyn.SCONexp scon => sconType scon (* 1 *)
	| Absyn.VIDexp(refLongVid, refOptIdStatus) => (* 2 *)
	  let val longvid = !refLongVid
	      val (longvidOpt, sigma, is) = lookupLongVid(C, longvid)
	      val _ = refOptIdStatus := SOME is
	      val _ = case longvidOpt
		       of NONE => ()
			| SOME longvid' =>
			  if longvid = longvid' then ()
			  else refLongVid := longvid'
	      val (_, tau) = Types.instFree(sigma, level)
	  in
	    tau
	  end
	| Absyn.RECexp exprow => (* 3 *)
	  let val rho = elabExprow(C, level, exprow)
	  in
	    Types.REC rho
	  end
	| Absyn.LETexp(dec, exp) => (* 4 *)
	  let val E = elabDec(C, level + 1, dec)
	      val tau = elabExp(cPlusE(C, E), level, exp)
	      (* TODO: "tynames tau <= T of C" side-condition *)
	  in
	    tau
	  end
	| Absyn.APPexp(f, arg) => (* 8 *)
	  let val tau'' = elabExp(C, level, f)
	      val tau' = elabExp(C, level, arg)
	      val tau = Types.VAR(Types.mkFreeTyvar level)
	      val _ = Unify.unify(tau'', funTy(tau', tau))
	  in
	    tau
	  end
	| Absyn.TYPEDexp(exp, ty) => (* 9 *)
	  let val tau = elabExp(C, level, exp)
	      val tau' = elabTy(C, ty)
	      val _ = Unify.unify(tau, tau')
	  in
	    tau
	  end
	| Absyn.HANDLEexp(exp, match) => (* 10 *)
	  let val tau = elabExp(C, level, exp)
	      val tau' = elabMatch(C, level, match)
	      val _ = Unify.unify(tau', funTy(Basis.exnTy, tau))
	  in
	    tau
	  end
	| Absyn.RAISEexp exp => (* 11 *)
	  let val _ = Unify.unify(elabExp(C, level, exp), Basis.exnTy)
	      val tau = Types.VAR(Types.mkFreeTyvar level)
	  in
	    tau
	  end
	| Absyn.FNexp match => (* 12 *)
	  elabMatch(C, level, match)

    and elabExprow(C, level, exprow) = (* C |- exprow => rho *)
      let val rho = List.foldl (elabExpRowField C level) [] exprow
	  val rho = Types.sortFields rho
	  val _ = checkRho rho
      in
	Types.mkRecord(rho, false)
      end

    and elabExpRowField C level ((label, exp), rho) = (* 6 *)
      let val tau = elabExp(C, level, exp)
      in
	(label, tau) :: rho
      end

    and elabMatch(C, level, Absyn.MATCH mrules) = (* C |- match => tau *)
      case mrules
       of mrule::mrules =>
	  List.foldl (elabMrule' C level) (elabMrule(C, level, mrule)) mrules
	| [] => raise TypeCheck

    and elabMrule' C level (mrule, tau) = (* 13 *)
      let val _ = Unify.unify(elabMrule(C, level, mrule), tau)
      in
	tau
      end

    and elabMrule(C, level, (pat, exp)) = (* C |- mrule => tau *) (* 14 *)
      let val (VE, tau) = elabPat(C, level, Types.genNone, Basis.emptyVE, pat)
	  val tau' = elabExp(cPlusVE(C, VE), level, exp)
	  (* TODO: "tynames VE <= T of C" side-condition *)
      in
	funTy(tau, tau')
      end

    (*
     * Declarations
     *)

    and elabDec(C, level, Absyn.DEC decs) = (* C |- dec => E *)
      List.foldl (elabDec' C level) Basis.emptyEnv decs

    and elabDec' C level (dec, E) =
      let val C = cPlusE(C, E)
      in
	case dec
	 of Absyn.VALdec(tyvarseqRef, nonrecs, recs) => (* 15 *)
	    let val VE = elabValbind(C, level, nonrecs, recs)
		(* Note: the closure is dony by elabValbind *)
		(* TODO: handle tyvarseq correctly *)
	    in
	      ePlusVE(E, VE)
	    end
	  | Absyn.TYPEdec typbind => (* 16 *)
	    let val TE = elabTypBind(C, typbind)
	    in
	      ePlusTE(E, TE)
	    end
	  | Absyn.DATATYPEdec(datbind, typbind) => (* 17 *)
	    let val (VE, TE) = elabDatBind(C, datbind, typbind)
	    in
	      ePlusTE(ePlusVE(E, VE), TE)
	    end
	  | Absyn.DATAREPLdec(tycon, longtycon) => (* 18 *)
	    let val Basis.TYSTR(tyfcn, VE) = lookupLongTyCon(C, longtycon)
		val TE = teBindTyCon(Basis.emptyTE, tycon, tyfcn, VE)
	    in
	      ePlusTE(ePlusVE(E, VE), TE)
	    end
	  | Absyn.EXdec exbind => (* 20 *)
	    let val VE = elabExBind(C, exbind)
	    in
	      ePlusVE(E, VE)
	    end
	  | Absyn.LOCALdec(dec1, dec2) => (* 21 *)
	    let val E1 = elabDec(C, level, dec1)
		val E2 = elabDec(cPlusE(C, E1), level, dec2)
	    in
	      ePlusE(E, E2)
	    end
	  | _ => nyi "abstype or open <dec>" (* 19 *) (* 22 *)
      end

    and elabValbind(C, level, nonrecs, recs) =
      elabValRec(C, level, List.foldl (elabValNonRec C level) Basis.emptyVE nonrecs, recs)

    and elabValNonRec C level ((pat, exp), VE) = (* 25 *)
      let val gen = if isNexp(C, exp) then fn tau => Types.genLimit(tau, level) else Types.genNone
	  val (VE, tau) = elabPat(C, level, gen, VE, pat)
	  val tau' = elabExp(C, level, exp)
	  val _ = Unify.unify(tau, tau')
      in
	VE
      end

    and elabValRec(C, level, VE, recs) =
      let val (VErec, recs') = List.foldl (elabValRecPat C level) (Basis.emptyVE, []) recs
	  (* Check the VErec for reserved identifiers.  They all have is "c",
	     so could normally not get bound, but VErec explicitly ignores is.  *)
	  val _ = checkValEnvVids VErec
	  val _ = List.app (elabValRecMatch (cPlusVE(C, VErec)) level) recs'
      in
	vePlusVE(VE, closVE(level, VErec))
      end

    and elabValRecMatch C level (tau, match) =
      Unify.unify(tau, elabMatch(C, level, match))

    (*
     * Value Descriptions
     *)

    fun elabValDesc' C ((vid, ty), VE) = (* 79 *)
      let val _ = checkValVid vid
	  val tau = elabTy(C, ty)
	  val sigma = Types.genAll tau
      in
	veBindVid(VE, vid, sigma, Basis.VAL)
      end

    fun elabValDesc(C, valdesc) = (* C |- valdesc => E *)
      List.foldl (elabValDesc' C) Basis.emptyVE valdesc

    (*
     * Type Descriptions
     *)

    fun elabTypDesc' C eq ((tyvarseq, tycon), TE) = (* 80 *)
      let val alphas = elabTyvarseq tyvarseq
	  val tyname = Types.TYNAME{strid = "FIXME", tycon = tycon, eq = ref eq}
	  val tau = Types.CONS(List.map Types.VAR alphas, tyname)
	  val tyfcn = Types.lambda(alphas, tau)
      in
	teBindTyCon(TE, tycon, tyfcn, Basis.emptyVE)
      end

    fun elabTypDesc(C, eq, typdesc) = (* C |- typdesc => TE *)
      List.foldl (elabTypDesc' C eq) Basis.emptyTE typdesc

    (*
     * Exception Descriptions
     *)

    fun elabExDesc' C ((vid, tyOpt), VE) = (* 83 *)
      let val (tau', hasArg) =
	      case tyOpt
	       of NONE => (Basis.exnTy, false)
		| SOME ty =>
		  (* TODO: (83) checks that tyvars(tau) is empty, but that would allow
		   * explicit type variables to occur but be forgotten; e.g. the following
		   * would elaborate:
		   *
		   * type 'a forget = int
		   * signature S = sig exception E of 'b forget end
		   *
		   * MoscowML rejects it but HaMLet accepts it.
		   *)
		  let val _ = checkFreeTyVars([], ty)
		      val tau = elabTy(C, ty)
		  in
		    (funTy(tau, Basis.exnTy), true)
		  end
	  val is = Basis.EXN hasArg
	  val sigma = Types.genNone tau'
      in
	veBindCon(VE, vid, sigma, is)
      end

    fun elabExDesc(C, Absyn.CONBIND conbind) = (* C |- exdesc => VE *)
      List.foldl (elabExDesc' C) Basis.emptyVE conbind

    (*
     * Structure Descriptions
     *)

    fun elabStrDesc(B, strdesc) = (* B |- strdesc => SE *)
      List.foldl (elabStrDesc' B) Basis.emptySE strdesc

    and elabStrDesc' B ((strid, sigexp), SE) = (* 84 *)
      let val E = elabSigExpE(B, sigexp)
      in
	seBindStrId(SE, strid, E)
      end

    (*
     * Specifications
     *)

    and elabSpec(B, Absyn.SPEC specs) = (* B |- spec => E *)
      List.foldl (elabSpec' B) Basis.emptyEnv specs

    and elabSpec' B (spec, E) =
      case spec
       of Absyn.VALspec valdesc => (* 68 *)
	  let val VE = elabValDesc(E, valdesc)
	      (* Note: the closure is done by elabValDesc *)
	  in
	    ePlusVE(E, VE)
	  end
	| Absyn.TYPEspec typdesc => (* 69 *)
	  let val TE = elabTypDesc(E, Types.NEVER, typdesc)
	  in
	    ePlusTE(E, TE)
	  end
	| Absyn.EQTYPEspec typdesc => (* 70 *)
	  let val TE = elabTypDesc(E, Types.ALWAYS, typdesc)
	  in
	    ePlusTE(E, TE)
	  end
	| Absyn.DATATYPEspec datbind => (* 71 *)
	    let val (VE, TE) = elabDatBind(E, datbind, Absyn.TYPBIND [])
	    in
	      ePlusTE(ePlusVE(E, VE), TE)
	    end
	| Absyn.DATAREPLspec(tycon, longtycon) => (* 72 *)
	  let val Basis.TYSTR(tyfcn, VE) = lookupLongTyCon(E, longtycon)
	      val TE = teBindTyCon(Basis.emptyTE, tycon, tyfcn, VE)
	  in
	    ePlusTE(ePlusVE(E, VE), TE)
	  end
	| Absyn.EXspec exdesc => (* 73 *)
	  let val VE = elabExDesc(E, exdesc)
	  in
	    ePlusVE(E, VE)
	  end
	| Absyn.STRUCTUREspec strdesc => (* 74 *)
	  let val SE = elabStrDesc(B, strdesc)
	  in
	    ePlusSE(E, SE)
	  end
	| Absyn.INCLUDEspec sigexp => (* 75 *)
	  let val E' = elabSigExpE(B, sigexp)
	  in
	    ePlusE(E, E')
	  end
	| Absyn.SHARINGTYspec _ => nyi "sharing type <spec>"
	| Absyn.SHARINGSTRspec _ => nyi "sharing <spec>"

    (*
     * Signature Expressions
     *)

    and elabSigExpE(B, sigexp) = (* B |- sigexp => E *)
      case sigexp
       of Absyn.SPECsigexp spec => (* 62 *)
	  let val E = elabSpec(B, spec)
	  in
	    E
	  end
	| Absyn.SIGIDsigexp sigid => (* 63 *)
	  let val Basis.SIG E = lookupSigId(B, sigid)
	      (* TODO: rename tynames? *)
	  in
	    E
	  end
	| Absyn.WHEREsigexp _ => nyi "where <sigexp" (* 64 *)

    fun elabSigExpSigma(B, sigexp) = (* B |- sigexp => sigma *) (* 65 *)
      let val E = elabSigExpE(B, sigexp)
	  (* TODO: bind tynames? *)
      in
	Basis.SIG E
      end

    (*
     * Signature Bindings
     *)

    fun elabSigBind' B ((sigid, sigexp), G) = (* 67 *)
      let val sigma = elabSigExpSigma(B, sigexp)
      in
	gBindSigId(G, sigid, sigma)
      end

    fun elabSigBind(B, Absyn.SIGBIND sigbinds) = (* B |- sigbind => G *)
      List.foldl (elabSigBind' B) Basis.emptyG sigbinds

    (*
     * STRUCTURES
     *)

    fun cOfB(Basis.BASIS(_, E)) = E

    fun bPlusE(Basis.BASIS(G, E1), E2) = Basis.BASIS(G, ePlusE(E1, E2))

    fun checkStrDec(B, Absyn.STRDEC[strdec]) = (* B |- strdec => E *)
        (case strdec
	  of Absyn.DECstrdec dec => elabDec(cOfB B, 0, dec)
	   | Absyn.LOCALstrdec(strdec1, strdec2) =>
	     let val E1 = checkStrDec(B, strdec1)
		 val E2 = checkStrDec(bPlusE(B, E1), strdec2)
	     in
	       E2
	     end
	   | _ => nyi "<strbind> form of <strdec>")
      | checkStrDec(_, _) = nyi "non-single <strdec>"

    fun checkModule(strdec, sigid, refOptEnv, basis) =
      let val _ = checkStrDec(Basis.emptyBasis, strdec)
	  val Basis.SIG env = lookupSigId(basis, sigid)
      in
	refOptEnv := SOME env;
	env
      end

    fun checkStrExp(strexp, basis) =
      case strexp
       of Absyn.TRANSPARENTstrexp(Absyn.STRUCTstrexp strdec, Absyn.SIGIDsigexp sigid, refOptEnv) =>
	  checkModule(strdec, sigid, refOptEnv, basis)
	| Absyn.OPAQUEstrexp(Absyn.STRUCTstrexp strdec, Absyn.SIGIDsigexp sigid, refOptEnv) =>
	  checkModule(strdec, sigid, refOptEnv, basis)
	| _ => nyi "non-plain form of <strexp>"

    fun bindStrid(Basis.BASIS(sigenv, Basis.E(Basis.SE dict, tyenv, valenv)), strid, env) =
      Basis.BASIS(sigenv, Basis.E(Basis.SE(Dict.insert(dict, strid, env)), tyenv, valenv))

    fun checkStrBind'((strid, strexp), basis) =
      bindStrid(basis, strid, checkStrExp(strexp, basis))

    fun checkStrBind(Absyn.STRBIND strbinds, basis) =
      List.foldl checkStrBind' basis strbinds

    fun checkTopStrDec'(strdec, basis) =
      case strdec
       of Absyn.DECstrdec _ => nyi "top-level plain <dec>"
	| Absyn.STRUCTUREstrdec strbind => checkStrBind(strbind, basis)
	| Absyn.LOCALstrdec _ => nyi "top-level 'local'"

    fun checkTopStrDec(Absyn.STRDEC strdecs, basis) =
      List.foldl checkTopStrDec' basis strdecs

    (*
     * TOP-LEVEL DECLARATIONS
     *)

    fun checkTopDec(topdec, basis) =
      case topdec
       of Absyn.STRDECtopdec strdec => checkTopStrDec(strdec, basis)
	| Absyn.SIGDECtopdec sigbind =>
	  let val G = elabSigBind(basis, sigbind)
	  in
	    bPlusG(basis, G)
	  end
	| Absyn.FUNDECtopdec _ => nyi "functor declarations"

    fun check topdec =
      let val _ = ExplicitTyVarScope.annotate topdec
      in
	checkTopDec(topdec, Basis.emptyBasis)
      end

  end
