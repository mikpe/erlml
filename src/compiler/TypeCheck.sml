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

    fun unbound(kind, strids, id) =
      error("unbound " ^ kind ^ " " ^ String.concatWith "." (strids @ [id]))
    fun unboundVid(strids, vid) = unbound("vid", strids, vid)
    fun unboundStrId(strids, strid) = unbound("strid", strids, strid)
    fun unboundTyCon(strids, tycon) = unbound("tycon", strids, tycon)
    fun unboundTyVar tyvar = unbound("tyvar", [], tyvar)

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
		 of SOME(Basis.BASIS(_, env)) => env
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
	     | SOME(longvid, idstatus) => SOME(SOME longvid, idstatus))
	| SOME idstatus => SOME(NONE, idstatus)

    fun lookupLongVid(env, Absyn.LONGID([], vid)) =
        (case lookupVid(env, vid)
	  of SOME(longVidOpt, idstatus) => (longVidOpt, idstatus)
	   | NONE => unboundVid([], vid))
      | lookupLongVid(env, Absyn.LONGID(strid :: strids, vid)) =
	let val env = lookupFirstStrId(env, strid)
	    val (Basis.E(_, _, Basis.VE dict), revpfx) = List.foldl lookupNextStrId (env, [strid]) strids
	in
          case Dict.find(dict, vid)
	   of SOME idstatus => (NONE, idstatus)
	    | NONE => unboundVid(List.rev revpfx, vid)
	end

    fun veBindVid(Basis.VE dict, vid, idstatus) = (* VE+{vid->idstatus}, but checks vid not in Dom(VE) *)
      case Dict.find(dict, vid)
       of NONE => Basis.VE(Dict.insert(dict, vid, idstatus))
	| SOME _ => error("vid " ^ vid ^ " already bound")

    fun vePlusVE(VE, Basis.VE VE') = (* VE+VE', but checks Dom(VE) and Dom(VE') are disjoint *)
      let fun bind(vid, idstatus, VE) = veBindVid(VE, vid, idstatus)
      in
	Dict.fold(bind, VE, VE')
      end

    fun cPlusVE(Basis.E(SE, TE, Basis.VE dict1), Basis.VE dict2) =
      Basis.E(SE, TE, Basis.VE(Dict.plus(dict1, dict2)))

    val ePlusVE = cPlusVE

    fun cPlusE(Basis.E(Basis.SE SE1, Basis.TE TE1, Basis.VE VE1), Basis.E(Basis.SE SE2, Basis.TE TE2, Basis.VE VE2)) =
      Basis.E(Basis.SE(Dict.plus(SE1, SE2)), Basis.TE(Dict.plus(TE1, TE2)), Basis.VE(Dict.plus(VE1, VE2)))

    val ePlusE = cPlusE

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

    fun elabTy(C, ty) = (* C |- ty => tau *)
      case ty
       of Absyn.VARty tyvar => Types.VAR(Types.RIGID tyvar)
	| Absyn.RECty tyrow => elabTyRow(C, tyrow)
	| Absyn.CONSty(tyseq, longtycon) => elabConsTy(C, tyseq, longtycon)
	| Absyn.FUNty(ty, ty') => Types.CONS([elabTy(C, ty), elabTy(C, ty')], Basis.funTyname)

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
     * PATTERNS
     *)

    fun checkPat(C, pat, VE) = (* C |- pat => (VE,tau) *)
      case pat
       of Absyn.WILDpat => VE
	| Absyn.SCONpat _ => VE
	| Absyn.VIDpat(longid, refOptIdStatus) =>
	  (case longid
	    of Absyn.LONGID([], vid) =>
	       (case lookupVid(C, vid)
		 of SOME(_, idstatus) => (refOptIdStatus := SOME idstatus; VE)
		  | NONE => (refOptIdStatus := SOME Basis.VAL; veBindVid(VE, vid, Basis.VAL)))
	     | _ => (refOptIdStatus := SOME(#2(lookupLongVid(C, longid))); VE))
	| Absyn.RECpat(row, false) => checkPatRow(C, row, VE)
	| Absyn.RECpat(_, true) => nyi "flexible record patterns"
	| Absyn.CONSpat(_, pat) => checkPat(C, pat, VE)
	| Absyn.TYPEDpat(pat, _) => checkPat(C, pat, VE)
	| Absyn.ASpat(vid, pat) =>
	  (case lookupVid(C, vid)
	    of NONE => ()
	     | SOME(_, Basis.VAL) => ()
	     | SOME(_, _) => error("vid " ^ vid ^ " is a constructor");
	   checkPat(C, pat, veBindVid(VE, vid, Basis.VAL)))

    and checkPatRow(C, row, VE) = (* C |- patrow => (VE,rho) *)
      let val (VE, _) = List.foldl (checkPatRowField C) (VE, []) row
      in
	VE
      end

    and checkPatRowField C ((lab, pat), (VE, labels)) =
      let val VE = checkPat(C, pat, VE)
      in
	if Util.member(lab, labels) then error("label " ^ labelToString lab ^ " already bound")
	else (VE, lab :: labels)
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
     * No datbind or exbind may bind "it".''
     *)
    fun allowedConbindVid vid =
      case vid
       of "true" => false
	| "false" => false
	| "nil" => false
	| "::" => false
	| "ref" => false
	| _ => true

    fun checkConbindVid vid =
      if allowedConbindVid vid then ()
      else error("invalid binding of " ^ vid)

    fun elabConbind' C tau ((vid, tyOpt), (VE, taus)) =
      let val _ = checkConbindVid vid
      in
	case tyOpt
	 of NONE => (veBindVid(VE, vid, Basis.CON false), taus)
	  | SOME ty =>
	    let val tau' = elabTy(C, ty)
	    in
	      (veBindVid(VE, vid, Basis.CON true), tau' :: taus)
	    end
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
       of Absyn.CONexb vid => veBindVid(VE, vid, Basis.EXN false)
	| Absyn.OFexb(vid, ty) =>
	  let val tau = elabTy(C, ty)
	  in
	    veBindVid(VE, vid, Basis.EXN true)
	  end
	| Absyn.EQexb(vid, longvid) =>
	  case #2(lookupLongVid(C, longvid))
	   of idstatus as Basis.EXN _ => veBindVid(VE, vid, idstatus)
	    | _ => error "exception aliasing non-exception"

    fun elabExBind(C, exbind) = (* C |- exbind => VE *)
      List.foldl (elabExBind' C) Basis.emptyVE exbind

    (*
     * EXPRESSIONS
     *)

    fun checkLetRecPat C ((pat, _), VE) = checkPat(C, pat, VE)

    fun checkExp(env, exp) =
      case exp
       of Absyn.SCONexp _ => ()
	| Absyn.VIDexp(refLongVid, refOptIdStatus) =>
	  let val longvid = !refLongVid
	      val (longvidOpt, idstatus) = lookupLongVid(env, longvid)
	      val _ = refOptIdStatus := SOME idstatus
	  in
	    case longvidOpt
	     of NONE => ()
	      | SOME longvid' =>
		if longvid = longvid' then ()
		else refLongVid := longvid'
	  end
	| Absyn.RECexp row => List.app (checkFieldExp env) row
	| Absyn.LETexp(dec, exp) => checkExp(cPlusE(env, checkDec(env, dec)), exp)
	| Absyn.APPexp(f, arg) => (checkExp(env, f); checkExp(env, arg))
	| Absyn.TYPEDexp(exp, _) => checkExp(env, exp)
	| Absyn.HANDLEexp(exp, match) => (checkExp(env, exp); checkMatch(env, match))
	| Absyn.RAISEexp exp => checkExp(env, exp)
	| Absyn.FNexp match => checkMatch(env, match)

    and checkFieldExp env (_, exp) = checkExp(env, exp)

    and checkMatch(C, Absyn.MATCH mrules) = (* C |- match => tau *)
      List.app (checkMrule C) mrules

    and checkMrule C (pat, exp) = (* C |- mrule => tau *)
      let val VE = checkPat(C, pat, Basis.emptyVE)
      in
	checkExp(cPlusVE(C, VE), exp)
      end

    and checkDec(C, Absyn.DEC decs) = (* C |- dec => E *)
      List.foldl (checkDec' C) Basis.emptyEnv decs

    and checkDec' C (dec, E) =
      let val C = cPlusE(C, E)
      in
	case dec
	 of Absyn.VALdec(_, nonrecs, recs) => ePlusVE(E, checkValBind(C, nonrecs, recs))
	  | Absyn.TYPEdec typbind => ePlusTE(E, elabTypBind(C, typbind))
	  | Absyn.DATATYPEdec(datbind, typbind) =>
	    let val (VE, TE) = elabDatBind(C, datbind, typbind)
	    in
	      ePlusTE(ePlusVE(E, VE), TE)
	    end
	  | Absyn.DATAREPLdec(tycon, longtycon) =>
	    let val Basis.TYSTR(tyfcn, VE) = lookupLongTyCon(C, longtycon)
	    in
	      ePlusTE(ePlusVE(E, VE), teBindTyCon(Basis.emptyTE, tycon, tyfcn, VE))
	    end
	  | Absyn.EXdec exbind => ePlusVE(E, elabExBind(C, exbind))
	  | Absyn.LOCALdec(dec1, dec2) =>
	    let val E1 = checkDec(C, dec1)
		val E2 = checkDec(cPlusE(C, E1), dec2)
	    in
	      ePlusE(E, E2)
	    end
	  | _ => nyi "abstype or open <dec>"
      end

    and checkValBind(C, nonrecs, recs) = (* C |- valbind => VE *)
      checkLetRecs(C, recs, List.foldl (checkLetNonRec C) Basis.emptyVE nonrecs)

    and checkLetNonRec C ((pat, exp), VE) = (checkExp(C, exp); checkPat(C, pat, VE))

    and checkLetRecs(C, recs, VE) =
      let val VErec = List.foldl (checkLetRecPat C) Basis.emptyVE recs
	  val _ = List.app (checkLetRecMatch (cPlusVE(C, VErec))) recs
      in
	vePlusVE(VE, VErec)
      end

    and checkLetRecMatch C (_, match) = checkMatch(C, match)

    (*
     * SPECIFICATIONS
     *)

    fun checkValDesc' C ((vid, _), VE) =
      (* TODO:
       * - check vid may be bound (not forbidden)
       * - elaborate ty and record that too
       *)
      veBindVid(VE, vid, Basis.VAL)

    fun checkValDesc(C, valdesc) = (* C |- valdesc => VE *)
      List.foldl (checkValDesc' C) Basis.emptyVE valdesc

    fun checkConBind' C mkis ((vid, tyOpt), VE) =
      (* TODO:
       * - check vid may be bound (not forbidden)
       * - elaborate tyOpt and record that too
       *)
      let val hasarg = case tyOpt of SOME _ => true
				  |  NONE => false
      in
	veBindVid(VE, vid, mkis hasarg)
      end

    fun checkConBind(C, mkis, Absyn.CONBIND conbinds) = (* C,tau |- conbind => VE *)
      List.foldl (checkConBind' C mkis) Basis.emptyVE conbinds

    fun checkDatBind' C ((_, _, conbind), VE) =
      (* TODO:
       * - check tycon may be bound
       * - compute equality attribute
       * - record tycon in TE
       *)
      vePlusVE(VE, checkConBind(C, Basis.CON, conbind))

    fun checkDatBind(C, Absyn.DATBIND datbinds) = (* C |- datbind => VE,TE *)
      List.foldl (checkDatBind' C) Basis.emptyVE datbinds

    fun checkSpec'(spec, env) =
      case spec
       of Absyn.VALspec valdesc => ePlusVE(env, checkValDesc(env, valdesc))
	| Absyn.TYPEspec _ => env (* TODO *)
	| Absyn.EQTYPEspec _ => env (* TODO *)
	| Absyn.DATATYPEspec datbind => ePlusVE(env, checkDatBind(env, datbind))
	| Absyn.DATAREPLspec _ => env (* FIXME: import idstatus for ctors *)
	| Absyn.EXspec conbind => ePlusVE(env, checkConBind(env, Basis.EXN, conbind))
	| Absyn.STRUCTUREspec _ => nyi "nested structure in <spec>"
	| Absyn.INCLUDEspec _ => nyi "include <spec>" (* TODO *)
	| Absyn.SHARINGTYspec _ => nyi "sharing type <spec>"
	| Absyn.SHARINGSTRspec _ => nyi "sharing <spec>"

    fun checkSpec(Absyn.SPEC specs, env) =
      Basis.SIG(List.foldl checkSpec' env specs)

    (*
     * SIGNATURE EXPRESSIONS & BINDINGS
     *)

    fun lookupSigid'(Basis.BASIS(Basis.SIGE dict, _), sigid) =
      Dict.find(dict, sigid)

    fun lookupSigid(basis, sigid) =
      case lookupSigid'(basis, sigid)
       of NONE => lookupSigid'(Basis.initialBasis, sigid)
	| sth => sth

    fun bindSigid(Basis.BASIS(Basis.SIGE dict, env), sigid, sigma) =
      (* TODO: check that sigid isn't already bound *)
      Basis.BASIS(Basis.SIGE(Dict.insert(dict, sigid, sigma)), env)

    fun findSigma(sigid, basis) =
      case lookupSigid(basis, sigid)
       of SOME sigma => SOME sigma
	| NONE =>
	  case readBasisFile(sigid, ".sig")
	   of NONE => NONE
	    | SOME basis => lookupSigid'(basis, sigid)

    fun checkSigid(sigid, basis) =
      case findSigma(sigid, basis)
       of SOME sigma => sigma
	| NONE => error("sigid " ^ sigid ^ " is unbound and no valid .basis file found")

    fun checkSigExp(sigexp, basis) =
      case sigexp
       of Absyn.SPECsigexp spec  => checkSpec(spec, Basis.emptyEnv)
	| Absyn.SIGIDsigexp sigid => checkSigid(sigid, basis)
	| Absyn.WHEREsigexp _ => nyi "where <sigexp"

    fun checkSigBind'((sigid, sigexp), basis) =
      bindSigid(basis, sigid, checkSigExp(sigexp, basis))

    fun checkSigBind(Absyn.SIGBIND sigbinds, basis) =
      List.foldl checkSigBind' basis sigbinds

    (*
     * STRUCTURES
     *)

    fun cOfB(Basis.BASIS(_, E)) = E

    fun bPlusE(Basis.BASIS(SIGE, E1), E2) = Basis.BASIS(SIGE, ePlusE(E1, E2))

    fun checkStrDec(B, Absyn.STRDEC[strdec]) = (* B |- strdec => E *)
        (case strdec
	  of Absyn.DECstrdec dec => checkDec(cOfB B, dec)
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
	  val Basis.SIG env = checkSigid(sigid, basis)
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
	| Absyn.SIGDECtopdec sigbind => checkSigBind(sigbind, basis)
	| Absyn.FUNDECtopdec _ => nyi "functor declarations"

    fun check topdec =
      let val _ = ExplicitTyVarScope.annotate topdec
      in
	checkTopDec(topdec, Basis.emptyBasis)
      end

  end
