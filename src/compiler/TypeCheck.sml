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

    fun readBasisFile(id, ext) =
      (* TODO: path for basis files? *)
      SOME(Basis.read(id ^ ext ^ ".basis")) handle _ => NONE

    (*
     * PATTERNS
     *)

    fun lookupLongVid'(Basis.E(_, Basis.VE dict), [], vid) = Dict.find(dict, vid)
      | lookupLongVid'(Basis.E(Basis.SE dict, _), strid :: strids, vid) =
	lookupLongVid'(valOf(Dict.find(dict, strid)), strids, vid)

    (* For a short VId we look it up first in the current Env, and then in the initial Basis.
       For a long VId, we look up the first StrId first in the current Env, then in the
       initial Basis, and lastly from a .basis file.  The resulting Env is then used to
       look up subsequent StrIds and finally the VId. *)

    fun lookupLongVid(Basis.E(_, Basis.VE dict), Absyn.LONGID([], vid)) =
        (case Dict.find(dict, vid)
	  of NONE =>
	     let val Basis.BASIS(_, Basis.E(_, Basis.VE dict)) = Basis.initialBasis
	     in
	       Dict.find(dict, vid)
	     end
	   | sth => sth)
      | lookupLongVid(Basis.E(Basis.SE dict, _), Absyn.LONGID(strid :: strids, vid)) =
	case Dict.find(dict, strid)
	 of SOME env => lookupLongVid'(env, strids, vid)
	  | NONE =>
	    let val Basis.BASIS(_, Basis.E(Basis.SE dict, _)) = Basis.initialBasis
	    in
	      case Dict.find(dict, strid)
	       of SOME env => lookupLongVid'(env, strids, vid)
		| NONE =>
		  case readBasisFile(strid, ".sml")
		   of SOME(Basis.BASIS(_, env)) => lookupLongVid'(env, strids, vid)
		    | NONE => NONE
	    end

    fun bindVid(Basis.E(strenv, Basis.VE dict), vid, idstatus) =
      Basis.E(strenv, Basis.VE(Dict.insert(dict, vid, idstatus)))

    fun checkPat(env, pat) =
      case pat
       of Absyn.WILDpat => env
	| Absyn.SCONpat _ => env
	| Absyn.VIDpat(longid, refOptIdStatus) =>
	  (case longid
	    of Absyn.LONGID([], vid) =>
	       (case lookupLongVid(env, longid)
		 of SOME idstatus => (refOptIdStatus := SOME idstatus; env)
		  | NONE => (refOptIdStatus := SOME Basis.VAL; bindVid(env, vid, Basis.VAL)))
	     | _ => (refOptIdStatus := SOME(valOf(lookupLongVid(env, longid))); env))
	| Absyn.RECpat(row, false) => List.foldl checkFieldPat env row
	| Absyn.RECpat(_, true) => nyi "flexible record patterns"
	| Absyn.CONSpat(_, pat) => checkPat(env, pat)
	| Absyn.TYPEDpat(pat, _) => checkPat(env, pat)
	| Absyn.ASpat(vid, pat) => checkPat(bindVid(env, vid, Basis.VAL), pat)

    and checkFieldPat((_, pat), env) = checkPat(env, pat)

    (*
     * EXPRESSIONS
     *)

    fun checkExp(env, exp) =
      case exp
       of Absyn.SCONexp _ => ()
	| Absyn.VIDexp(longid, refOptIdStatus) => refOptIdStatus := SOME(valOf(lookupLongVid(env, longid)))
	| Absyn.RECexp row => List.app (checkFieldExp env) row
	| Absyn.LETexp(Absyn.DEC decs, exp) => checkExp(checkLetDecs(decs, env), exp)
	| Absyn.APPexp(f, arg) => (checkExp(env, f); checkExp(env, arg))
	| Absyn.TYPEDexp(exp, _) => checkExp(env, exp)
	| Absyn.HANDLEexp(exp, match) => (checkExp(env, exp); checkMatch(env, match))
	| Absyn.RAISEexp exp => checkExp(env, exp)
	| Absyn.FNexp match => checkMatch(env, match)

    and checkFieldExp env (_, exp) = checkExp(env, exp)

    and checkMatch(env, Absyn.MATCH clauses) = List.app (checkClause env) clauses

    and checkClause env (pat, exp) = checkExp(checkPat(env, pat), exp)

    and checkLetDecs([], env) = env
      | checkLetDecs(dec :: decs, env) = checkLetDecs(decs, checkLetDec(dec, env))

    and checkLetDec(dec, env) =
      case dec
       of Absyn.VALdec(_, nonrecs, recs) => checkLetRecs(recs, checkLetNonRecs(nonrecs, env))
	| _ => nyi "type, exception, local, or open form of <dec> in LET"

    and checkLetNonRecs([], env) = env
      | checkLetNonRecs((pat, exp) :: nonrecs, env) =
	(checkExp(env, exp); checkLetNonRecs(nonrecs, checkPat(env, pat)))

    and checkLetRecs(recs, env) =
      let val env' = checkLetRecPats(recs, env)
	  val _ = List.app (checkLetRecMatch env') recs
      in
	env'
      end

    and checkLetRecPats([], env) = env
      | checkLetRecPats((pat, _) :: recs, env) =
	checkLetRecPats(recs, checkPat(env, pat))

    and checkLetRecMatch env (_, match) = (checkMatch(env, match); ())

    (*
     * SPECIFICATIONS
     *)

    fun checkValSpecs([], env) = env
      | checkValSpecs((vid, _) :: valspecs, env) =
	(* TODO:
	 * - check vid may be bound (not bound in env, not forbidden)
	 * - elaborate ty and record that too
	 *)
	checkValSpecs(valspecs, bindVid(env, vid, Basis.VAL))

    fun checkConBinds([], _, env) = env
      | checkConBinds((vid, tyOpt) :: conbinds, mkis, env) =
	(* TODO:
	 * - check vid may be bound (not bound in env, not forbidden)
	 * - elaborate tyOpt and record that too
	 *)
	let val hasarg = case tyOpt of SOME _ => true
				    |  NONE => false
	in
	  checkConBinds(conbinds, mkis, bindVid(env, vid,  mkis hasarg))
	end

    fun checkDatBinds([], _, env) = env
      | checkDatBinds((_, _, Absyn.CONBIND conbinds) :: datbinds, mkis, env) =
	(* TODO:
	 * - check tycon may be bound
	 * - compute equality attribute
	 * - record tycon in TE
	 *)
	checkDatBinds(datbinds, mkis, checkConBinds(conbinds, mkis, env))

    fun checkSpec(spec, env) =
      case spec
       of Absyn.VALspec valspecs => checkValSpecs(valspecs, env)
	| Absyn.TYPEspec _ => env (* TODO *)
	| Absyn.EQTYPEspec _ => env (* TODO *)
	| Absyn.DATATYPEspec(Absyn.DATBIND datbinds) => checkDatBinds(datbinds, Basis.CON, env)
	| Absyn.DATAREPLspec _ => env (* TODO *)
	| Absyn.EXspec(Absyn.CONBIND conbinds) => checkConBinds(conbinds, Basis.EXN, env)
	| Absyn.STRUCTUREspec _ => nyi "nested structure in <spec>"
	| Absyn.INCLUDEspec _ => nyi "include <spec>" (* TODO *)
	| Absyn.SHARINGTYspec _ => nyi "sharing type <spec>"
	| Absyn.SHARINGSTRspec _ => nyi "sharing <spec>"

    fun checkSpecs([], env) = Basis.SIG env
      | checkSpecs(spec :: specs, env) = checkSpecs(specs, checkSpec(spec, env))

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
       of Absyn.SPECsigexp(Absyn.SPEC specs) => checkSpecs(specs, Basis.emptyEnv)
	| Absyn.SIGIDsigexp sigid => checkSigid(sigid, basis)
	| Absyn.WHEREsigexp _ => nyi "where <sigexp"

    fun checkSigBinds([], basis) = basis
      | checkSigBinds((sigid, sigexp) :: sigbinds, basis) =
	checkSigBinds(sigbinds, bindSigid(basis, sigid, checkSigExp(sigexp, basis)))

    (*
     * STRUCTURES
     *)

    fun checkExBind(exb, env) =
      case exb
       of Absyn.CONexb vid => bindVid(env, vid, Basis.EXN false)
	| Absyn.OFexb(vid, _) => bindVid(env, vid, Basis.EXN true)
	| Absyn.EQexb(vid, longvid) =>
	  case lookupLongVid(env, longvid)
	   of SOME(idstatus as Basis.EXN _) => bindVid(env, vid, idstatus)
	    | SOME _ => error "exception aliasing non-exception"
	    | NONE => error "exception aliasing unbound identifier"

    fun checkExBinds([], env) = env
      | checkExBinds(exb :: exbinds, env) =
	checkExBinds(exbinds, checkExBind(exb, env))

    fun checkDec(dec, env) =
      case dec
       of Absyn.VALdec(_, nonrecs, recs) => checkLetRecs(recs, checkLetNonRecs(nonrecs, env))
	| Absyn.TYPEdec _ => env
	| Absyn.DATATYPEdec(Absyn.DATBIND datbinds, _) => checkDatBinds(datbinds, Basis.CON, env)
	| Absyn.DATAREPLdec _ => env
	| Absyn.EXdec exbinds => checkExBinds(exbinds, env)
	| _ => nyi "abstype, local, or open form of structure-level <dec>"

    fun checkDecs([], env) = env
      | checkDecs(dec :: decs, env) = checkDecs(decs, checkDec(dec, env))

    fun checkModule(Absyn.DEC decs, sigid, refOptEnv, basis) =
      let val _ = checkDecs(decs, Basis.emptyEnv)
	  val Basis.SIG env = checkSigid(sigid, basis)
      in
	refOptEnv := SOME env;
	env
      end

    fun checkStrExp(strexp, basis) =
      case strexp
       of Absyn.TRANSPARENTstrexp(Absyn.STRUCTstrexp(Absyn.STRDEC[Absyn.DECstrdec dec]), Absyn.SIGIDsigexp sigid, refOptEnv) =>
	  checkModule(dec, sigid, refOptEnv, basis)
	| Absyn.OPAQUEstrexp(Absyn.STRUCTstrexp(Absyn.STRDEC[Absyn.DECstrdec dec]), Absyn.SIGIDsigexp sigid, refOptEnv) =>
	  checkModule(dec, sigid, refOptEnv, basis)
	| _ => nyi "non-plain form of <strexp>"

    fun bindStrid(Basis.BASIS(sigenv, Basis.E(Basis.SE dict, valenv)), strid, env) =
      Basis.BASIS(sigenv, Basis.E(Basis.SE(Dict.insert(dict, strid, env)), valenv))

    fun checkStrBinds([], basis) = basis
      | checkStrBinds((strid, strexp) :: strbinds, basis) =
	checkStrBinds(strbinds, bindStrid(basis, strid, checkStrExp(strexp, basis)))

    fun checkStrDec(strdec, basis) =
      case strdec
       of Absyn.DECstrdec _ => nyi "top-level plain <dec>"
	| Absyn.STRUCTUREstrdec(Absyn.STRBIND strbinds) => checkStrBinds(strbinds, basis)
	| Absyn.LOCALstrdec _ => nyi "top-level 'local'"

    fun checkStrDecs([], basis) = basis
      | checkStrDecs(strdec :: strdecs, basis) =
	checkStrDecs(strdecs, checkStrDec(strdec, basis))

    (*
     * TOP-LEVEL DECLARATIONS
     *)

    fun checkTopDec(topdec, basis) =
      case topdec
       of Absyn.STRDECtopdec(Absyn.STRDEC strdecs) => checkStrDecs(strdecs, basis)
	| Absyn.SIGDECtopdec(Absyn.SIGBIND sigbinds) => checkSigBinds(sigbinds, basis)
	| Absyn.FUNDECtopdec _ => nyi "functor declarations"

    fun check topdec = checkTopDec(topdec, Basis.emptyBasis)

  end
