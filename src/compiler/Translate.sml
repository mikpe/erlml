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
structure Translate : TRANSLATE =
  struct

    exception Translate

    fun sayErr s = TextIO.output(TextIO.stdErr, s)

    fun nyi msg =
      (sayErr("translate: nyi " ^ msg ^ "\n"); raise Translate)

    (*
     * PATTERNS
     *)

    fun transScon scon =
      case scon
       of Absyn.INTsc i => CoreErlang.L_INTEGER i
	| Absyn.WORDsc i => CoreErlang.L_INTEGER i
	| Absyn.REALsc r => CoreErlang.L_FLOAT r
	| Absyn.STRINGsc s => CoreErlang.L_STRING s
	| Absyn.CHARsc c => CoreErlang.L_INTEGER(IntInf.fromInt(Char.ord c))

    fun recordToTuple row =
      let fun labelLt(Absyn.INTlab i1, Absyn.INTlab i2) = i1 < i2
	    | labelLt(Absyn.INTlab _, Absyn.IDlab _) = true
	    | labelLt(Absyn.IDlab i1, Absyn.IDlab i2) = i1 < i2
	    | labelLt(Absyn.IDlab _, Absyn.INTlab _) = false
	  fun insert(item, []) = [item]
	    | insert(item1 as (lab1,_), row as ((item2 as (lab2,_)) :: row')) =
	      if labelLt(lab1, lab2) then item1 :: row else item2 :: insert(item1, row')
      in
	List.map #2 (List.foldl insert [] row)
      end

    fun transPat pat =
      case pat
       of Absyn.WILDpat => CoreErlang.P_VARIABLE(CoreErlang.mkVar NONE)
	| Absyn.SCONpat scon => CoreErlang.P_LITERAL(transScon scon)
	| Absyn.VIDpat(longid as Absyn.LONGID(_, vid), refOptIdStatus) =>
	  (* TODO:
	   * - allow for different con rep than atoms (e.g. fixnums or nil)
	   * - proper SML semantics for exn con (generative, alias)?
	   *)
	  (case valOf(!refOptIdStatus)
	    of Basis.VAL => CoreErlang.P_VARIABLE vid
	     | _ => CoreErlang.P_LITERAL(CoreErlang.L_ATOM vid))
	| Absyn.RECpat(row, false) => CoreErlang.P_TUPLE(List.map transPat (recordToTuple row))
	| Absyn.RECpat(_, true) => nyi "flexible record patterns"
	| Absyn.CONSpat(Absyn.LONGID(_, con), pat) =>
	  CoreErlang.P_TUPLE [CoreErlang.P_LITERAL(CoreErlang.L_ATOM con), transPat pat]
	| Absyn.TYPEDpat(pat, _) => transPat pat
	| Absyn.ASpat(_, pat) => transPat pat

    (*
     * EXPRESSIONS
     *)

    fun recbindFname(Absyn.VIDpat(Absyn.LONGID([], id), _)) = CoreErlang.FNAME(id, 1)
      | recbindFname(_) = nyi "bad function name pattern in 'let val rec'"

    fun mkFnameAlias((fname as CoreErlang.FNAME(id, _), _), body) =
      CoreErlang.E_LET(id, CoreErlang.E_FNAME fname, body)

    fun mkCall(m, f, args) =
      CoreErlang.E_CALL(CoreErlang.E_LITERAL(CoreErlang.L_ATOM m),
			CoreErlang.E_LITERAL(CoreErlang.L_ATOM f),
			args)

    fun callErlang(f, args) = mkCall("erlang", f, args)

    fun callErlmlRuntime(f, args) = mkCall("erlml_runtime", f, args)

    fun transConExp(vid, hasarg) =
      let val tagExp = CoreErlang.E_LITERAL(CoreErlang.L_ATOM vid)
      in
	case hasarg
	 of false => tagExp
	  | true =>
	    let val var = CoreErlang.mkVar NONE
		val bodyExp = CoreErlang.E_TUPLE[tagExp, CoreErlang.E_VARIABLE var]
	    in
	      CoreErlang.E_FUN(CoreErlang.FUN([var], bodyExp))
	    end
      end

    fun transVarExp(Absyn.LONGID(strids, vid)) =
      case strids
       of [] => CoreErlang.E_VARIABLE vid
	| [strid] => mkCall(strid, vid, [])
	| _ => nyi "nested structures in <longid> expressions"

    fun transExp exp =
      case exp
       of Absyn.SCONexp scon => CoreErlang.E_LITERAL(transScon scon)
	| Absyn.VIDexp(longid as Absyn.LONGID(_, vid), refOptIdStatus) =>
	  (* TODO:
	   * - allow for different con rep than atoms (e.g. fixnum or nil)
	   * - proper SML semantics for exn con (generative, alias)?
	   *)
	  (case valOf(!refOptIdStatus)
	    of Basis.VAL => transVarExp longid
	     | Basis.CON hasarg => transConExp(vid, hasarg)
	     | Basis.EXN hasarg => transConExp(vid, hasarg))
	| Absyn.RECexp row => CoreErlang.E_TUPLE(List.map transExp (recordToTuple row))
	| Absyn.LETexp(Absyn.DEC decs, exp) => transLet(decs, transExp exp)
	| Absyn.APPexp(f, arg) =>
	  let val var = CoreErlang.mkVar NONE
	  in
	    CoreErlang.E_LET(var, transExp f, CoreErlang.E_APPLY(CoreErlang.FV var, [transExp arg]))
	  end
	| Absyn.TYPEDexp(exp, _) => transExp exp
	| Absyn.HANDLEexp(exp, match) =>
	  let val e1 = transExp exp
	      val v1 = CoreErlang.mkVar NONE
	      val e2 = CoreErlang.E_VARIABLE v1
	      val cv1 = CoreErlang.mkVar NONE
	      val cv2 = CoreErlang.mkVar NONE
	      val cv3 = CoreErlang.mkVar NONE
	      val default = CoreErlang.E_PRIMOP("raise", [CoreErlang.E_VARIABLE cv3, CoreErlang.E_VARIABLE cv2])
	      val ce = transMatch(cv2, match, default)
	  in
	    CoreErlang.E_TRY(e1, v1, e2, cv1, cv2, cv3, ce)
	  end
	| Absyn.RAISEexp exp =>
	  (* TODO: currently all SML exceptions will have class 'throw',
	   * figure out a way to generate and handle ones with other classes,
	   * including native Erlang non-throw exceptions
	   *)
	  callErlang("throw", [transExp exp])
	| Absyn.FNexp match =>
	  let val var = CoreErlang.mkVar NONE
	      val default = callErlmlRuntime("raise_match", [])
	  in
	    CoreErlang.E_FUN(CoreErlang.FUN([var], transMatch(var, match, default)))
	  end

    and transMatch(var, Absyn.MATCH clauses, default) =
      CoreErlang.E_CASE(CoreErlang.E_VARIABLE var,
			(List.map transClause clauses) @
			[(CoreErlang.P_VARIABLE(CoreErlang.mkVar NONE), default)])

    and transClause(pat, exp) = (transPat pat, transExp exp)

    and transLet([], body) = body
      | transLet(dec :: decs, body) = transLetDec(dec, transLet(decs, body))

    and transLetDec(dec, body) =
      case dec
       of Absyn.VALdec(_, nonrecs, recs) => transLetVal(nonrecs, transLetRec(recs, body))
	| _ => nyi "type, exception, local, or open form of <dec> in LET"

    and transLetVal([(pat,exp)], body) =
	CoreErlang.E_CASE(transExp exp,
			  [(transPat pat, body),
			   (CoreErlang.P_VARIABLE(CoreErlang.mkVar NONE),
			    callErlmlRuntime("raise_bind", []))])
      | transLetVal([], body) = body
      | transLetVal(_, _) = nyi "multiple bindings in 'let val'"

    and transLetRec(recs, body) =
      let val fundefs = List.map transOneRecBind recs
      in
	CoreErlang.E_LETREC(List.map transOneRecBind recs,
			    List.foldl mkFnameAlias body fundefs)
      end

    and transOneRecBind(pat, match) =
      let val fname = recbindFname pat
	  val var = CoreErlang.mkVar NONE
	  val default = callErlmlRuntime("raise_match", [])
      in
	(fname, CoreErlang.FUN([var], transMatch(var, match, default)))
      end

    (*
     * STRUCTURES
     *)

    fun transDec(dec, body) =
      case dec
       of Absyn.VALdec(_, nonrecs, recs) => transLetVal(nonrecs, transLetRec(recs, body))
	| Absyn.TYPEdec _ => body
	| Absyn.DATATYPEdec _ => body
	| Absyn.DATAREPLdec _ => body
	| Absyn.EXdec _ => body (* TODO: proper SML semantics for exn con (generative, alias)? *)
	| _ => nyi "abstype, local, or open form of structure-level <dec>"

    fun transDecs([], body) = body
      | transDecs(dec :: decs, body) = transDec(dec, transDecs(decs, body))

    (*
     * MODULES
     *)

    fun mkModinfo0 modExp =
      (CoreErlang.FNAME("module_info", 0),
       CoreErlang.FUN([], callErlang("get_module_info", [modExp])))

    fun mkModinfo1 modExp =
      let val var = CoreErlang.mkVar NONE
      in
	(CoreErlang.FNAME("module_info", 1),
	 CoreErlang.FUN([var], callErlang("get_module_info", [modExp, CoreErlang.E_VARIABLE var])))
      end

    fun veToFunDef strid (vid, idstatus, fundefs) =
      case idstatus
       of Basis.VAL =>
	  let val vidkey = CoreErlang.E_TUPLE[CoreErlang.E_LITERAL(CoreErlang.L_ATOM strid),
					      CoreErlang.E_LITERAL(CoreErlang.L_ATOM vid)]
	      val fbody = callErlmlRuntime("get_var", [vidkey])
	  in
	    (CoreErlang.FNAME(vid, 0), CoreErlang.FUN([], fbody)) :: fundefs
	  end
	| _ => fundefs

    fun mkCtor strid (CoreErlang.FNAME(vid, _), ctor) =
      let val vidkey = CoreErlang.E_TUPLE[CoreErlang.E_LITERAL(CoreErlang.L_ATOM strid),
					  CoreErlang.E_LITERAL(CoreErlang.L_ATOM vid)]
      in
	CoreErlang.E_LET(CoreErlang.mkVar NONE, callErlmlRuntime("set_var", [vidkey, CoreErlang.E_VARIABLE vid]),
			 ctor)
      end

    fun transEnv(strid, Basis.E(_, Basis.VE ve)) =
      let val fundefs = Dict.fold(veToFunDef strid, [], ve)
	  val exports = List.map #1 fundefs
	  val ctor = List.foldl (mkCtor strid) (CoreErlang.E_LITERAL(CoreErlang.L_ATOM "ok")) exports
      in
	(exports, fundefs, ctor)
      end

    fun transModule(env, strid, Absyn.DEC decs) =
      let val (exports, fundefs, ctor) = transEnv(strid, env)
	  val ctor = transDecs(decs, ctor)
	  val ctordef = (CoreErlang.FNAME("ctor", 0), CoreErlang.FUN([], ctor))
	  val modExp = CoreErlang.E_LITERAL(CoreErlang.L_ATOM strid)
	  val (modinfo0 as (fname0, _)) = mkModinfo0 modExp
	  val (modinfo1 as (fname1, _)) = mkModinfo1 modExp
      in
	CoreErlang.MODULE(strid,
			  fname0 :: fname1 :: exports,
			  [("on_load",
			    CoreErlang.C_CONS(CoreErlang.C_TUPLE[CoreErlang.C_LITERAL(CoreErlang.L_ATOM "ctor"),
								 CoreErlang.C_LITERAL(CoreErlang.L_INTEGER(IntInf.fromInt 0))],
					      CoreErlang.C_LITERAL CoreErlang.L_NIL))],
			  modinfo0 :: modinfo1 :: ctordef :: fundefs)
      end

    fun transStrExp(strid, strexp) =
      case strexp
       of Absyn.TRANSPARENTstrexp(Absyn.STRUCTstrexp(Absyn.STRDEC[Absyn.DECstrdec dec]), _, refOptEnv) =>
	  transModule(valOf(!refOptEnv), strid, dec)
	| Absyn.OPAQUEstrexp(Absyn.STRUCTstrexp(Absyn.STRDEC[Absyn.DECstrdec dec]), _, refOptEnv) =>
	  transModule(valOf(!refOptEnv), strid, dec)
	| _ => nyi "non-plain form of <strexp>"

    fun transStrDecs strdecs =
      case strdecs
       of [Absyn.STRUCTUREstrdec(Absyn.STRBIND[(strid, strexp)])] =>
	  transStrExp(strid, strexp)
	| _ => nyi "non-plain kind of <strdec>"

    fun translate topdec =
      case topdec
       of Absyn.STRDECtopdec(Absyn.STRDEC strdecs) => transStrDecs strdecs
	  | _ => nyi "non-<strdec> kind of <topdec>"

  end
