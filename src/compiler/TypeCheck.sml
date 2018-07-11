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
     * DATATYPE and EXCEPTION declarations
     *)

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

    fun checkExBind' C (exb, VE) =
      case exb
       of Absyn.CONexb vid => veBindVid(VE, vid, Basis.EXN false)
	| Absyn.OFexb(vid, _) => veBindVid(VE, vid, Basis.EXN true)
	| Absyn.EQexb(vid, longvid) =>
	  case #2(lookupLongVid(C, longvid))
	   of idstatus as Basis.EXN _ => veBindVid(VE, vid, idstatus)
	    | _ => error "exception aliasing non-exception"

    fun checkExBind(C, exbind) = (* C |- exbind => VE *)
      List.foldl (checkExBind' C) Basis.emptyVE exbind

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
	  | Absyn.TYPEdec _ => E
	  | Absyn.DATATYPEdec(datbind, _) => ePlusVE(E, checkDatBind(C, datbind))
	  | Absyn.DATAREPLdec _ => E (* FIXME: import idstatus for ctors *)
	  | Absyn.EXdec exbind => ePlusVE(E, checkExBind(C, exbind))
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
