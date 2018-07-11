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
structure Basis : BASIS =
  struct

    type ident        = string	(* TODO: for now *)
    val identCompare  = String.compare

    datatype longid   = LONGID of ident list * ident

    datatype label    = datatype Types.label

    datatype idstatus = CON of bool (* hasarg? *)
		      | EXN of bool (* hasarg? *)
		      | VAL
    datatype valenv   = VE of (ident, idstatus) Dict.dict (* TODO: add TypeScheme *)

    datatype tystr    = TYSTR of Types.tyfcn * valenv
    datatype tyenv    = TE of (ident, tystr) Dict.dict

    datatype env      = E of strenv * tyenv * valenv
    and strenv        = SE of (ident, env) Dict.dict

    datatype sigma    = SIG of env (* TODO: add TyNameSet? *)
    datatype sigenv   = SIGE of (ident, sigma) Dict.dict

    datatype basis    = BASIS of sigenv * env (* TODO: add FunEnv *)

    val emptyVE = VE(Dict.empty identCompare)

    val emptyTE = TE(Dict.empty identCompare)

    val emptySE = SE(Dict.empty identCompare)

    val emptyEnv = E(emptySE, emptyTE, emptyVE)

    val emptySIGE = SIGE(Dict.empty identCompare)

    val emptyBasis = BASIS(emptySIGE, emptyEnv)

    (* Initial Basis (TODO: incomplete) *)

    val veTextIO = VE(Dict.fromList(identCompare, [("output", VAL), ("stdOut", VAL)]))

    val stridPrimitive = "_ERLML_PRIMITIVE"
    val toplevelValEnv =
	Dict.fromList(identCompare,
		      [ ("true", (LONGID([stridPrimitive], "true"), CON false))
		      , ("false", (LONGID([stridPrimitive], "false"), CON false))
		      , ("NONE", (LONGID(["Option"], "NONE"), CON false))
		      , ("SOME", (LONGID(["Option"], "SOME"), CON true))
		      , ("nil", (LONGID([stridPrimitive], "nil"), CON false))
		      , ("::", (LONGID([stridPrimitive], "::"), CON true))
		      , ("=", (LONGID([stridPrimitive], "="), VAL))
		      , ("<", (LONGID([stridPrimitive], "<"), VAL))
		     ])
    val toplevelTyEnv = emptyTE

    val initialSigEnv = emptySIGE
    val initialValEnv = emptyVE
    val initialTyEnv = emptyTE
    val initialStrEnv = SE(Dict.fromList(identCompare, [("TextIO", E(emptySE, emptyTE, veTextIO))]))
    val initialEnv = E(initialStrEnv, initialTyEnv, initialValEnv)
    val initialBasis = BASIS(initialSigEnv, initialEnv)

    (* File I/O of basis objects *)

    exception Basis

    fun error msg =
      (TextIO.output(TextIO.stdErr, "Error reading basis file: " ^ msg ^ "\n"); raise Basis)

    fun prematureEof wanted =
      error("expected " ^ wanted ^ ", got premature eof")

    fun expected(wanted, got) =
      error("expected " ^ wanted ^ ", got " ^ Char.toString got)

    fun readEof is =
      case TextIO.endOfStream is
       of true => ()
	| false => error "trailing garbage"

    fun readChar(is, wanted) =
      case TextIO.input1 is
       of SOME c => if c = wanted then () else expected(Char.toString wanted, c)
	| NONE => prematureEof(Char.toString wanted)

    (* I/O of version marker at start of basis file *)

    val version = #"0"

    fun writeVersion os =
      TextIO.output1(os, version)

    fun readVersion is =
      readChar(is, version)

    (* I/O of identifiers *)

    fun writeIdent(os, ident) =
      (TextIO.output1(os, #"\"");
       TextIO.output(os, ident);
       TextIO.output1(os, #"\""))

    fun readIdent is =
      let val _ = readChar(is, #"\"")
	  fun loop cs =
	    case TextIO.input1 is
	     of SOME #"\"" => String.implode(List.rev cs)
	      | SOME c => loop(c :: cs)
	      | NONE => prematureEof "identifier"
      in
	loop []
      end

    (* I/O of non-negative integers *)

    fun writeInt(os, i) =
      writeIdent(os, Int.toString i)

    fun readInt is =
      case Int.fromString(readIdent is)
       of SOME i => i
	| NONE => error "invalid numeral"

    (* I/O of IdStatus *)

    fun writeIdStatus(os, idStatus) =
      let val (c, hasargOpt) =
	      case idStatus
	       of CON hasarg => (#"c", SOME hasarg)
		| EXN hasarg => (#"e", SOME hasarg)
		| VAL => (#"v", NONE)
      in
	TextIO.output1(os, c);
	case hasargOpt
	 of SOME false => TextIO.output1(os, #"0")
	  | SOME true => TextIO.output1(os, #"1")
	  | NONE => ()
      end

    fun readIdStatus is =
      let fun readHasArg is =
	    case TextIO.input1 is
	     of SOME #"0" => false
	      | SOME #"1" => true
	      | SOME c => expected("constatus hasarg (0|1)", c)
	      | NONE => prematureEof "constatus hasarg (0|1)"
      in
	case TextIO.input1 is
	 of SOME #"c" => CON(readHasArg is)
	  | SOME #"e" => EXN(readHasArg is)
	  | SOME #"v" => VAL
	  | SOME c => expected("idstatus (c|e|v)", c)
	  | NONE => prematureEof "idstatus (c|e|v)"
      end

    (* I/O of Dict.dict *)

    fun writeDict(os, dict, writeMapping) =
      (TextIO.output1(os, #"[");
       Dict.fold(writeMapping, os, dict);
       TextIO.output1(os, #"]"))

    fun readDict(is, readMapping) =
      let val _ = readChar(is, #"[")
	  fun loop dict =
	    case TextIO.lookahead is
	     of SOME #"]" => (readChar(is, #"]"); dict)
	      | _ => loop(readMapping(is, dict))
      in
	loop(Dict.empty identCompare)
      end

    (* I/O of types *)

    fun writeLabel(os, label) =
      case label
       of Types.IDlab ident => writeIdent(os, ident)
	| Types.INTlab i => writeInt(os, i)

    fun readLabel is =
      let val ident = readIdent is
      in
	case Int.fromString ident
	 of SOME i => Types.INTlab i
	  | NONE => Types.IDlab ident
      end

    (* Since the key contains a ref and there is no compare function for refs,
       we use an association list instead. *)
    datatype alphamap = AM of {next: int, alist: (Types.alpha * int) list}

    val alphaMapEmpty = AM{next = 0, alist = []}

    fun findAlphaFromIndex(AM{alist = alist, ...}, index) =
      let fun find((alpha, i) :: alist) = if i = index then SOME alpha else find alist
	    | find([]) = NONE
      in
	find alist
      end

    fun updateAlphaMap(alphaMap as AM{next = next, alist = alist}, index, alpha) =
      case findAlphaFromIndex(alphaMap, index)
       of NONE => AM{next = index + 1, alist = (alpha, index) :: alist}
	| SOME _ => error "updateAlphaMap"

    fun findTyvar(alphaMap as AM{next = next, alist = alist}, alpha) =
      case Util.bound(alist, alpha)
       of SOME i => (true, alphaMap, i)
	| NONE =>
	  let val next = next + 1
	      val alist = (alpha, next) :: alist
	  in
	    (false, AM{next = next, alist = alist}, next)
	  end

    fun writeTyname(os, Types.TYNAME{strid = strid, tycon = tycon, eq = eq}) =
      (writeIdent(os, strid);
       TextIO.output1(os, #".");
       writeIdent(os, tycon);
       TextIO.output1(os, case eq of Types.NEVER => #"n"
				   | Types.MAYBE => #"m"
				   | Types.ALWAYS => #"a"))

    fun readTyname is =
      let val strid = readIdent is
	  val _ = readChar(is, #".")
	  val tycon = readIdent is
	  val eq =
	      case TextIO.input1 is
	       of SOME #"n" => Types.NEVER
		| SOME #"m" => Types.MAYBE
		| SOME #"a" => Types.ALWAYS
		| SOME c => expected("n, m, or a", c)
		| NONE => prematureEof "n, m, or a"
      in
	Types.TYNAME{strid = strid, tycon = tycon, eq = eq}
      end

    fun writeList(os, write, state, xs) =
      let val _ = TextIO.output1(os, #"<")
	  val state = List.foldl (fn(state, x) => write(os, state, x)) state xs
	  val _ = TextIO.output1(os, #">")
      in
	state
      end

    fun readList(is, read, state) = (* TODO: merge with readDict *)
      let val _ = readChar(is, #"<")
	  fun loop(acc, state) =
	    case TextIO.lookahead is
	     of SOME #">" => (readChar(is, #">"); (List.rev acc, state))
	      | _ =>
		let val (item, state) = read(is, state)
		in
		  loop(item :: acc, state)
		end
      in
	loop([], state)
      end

    fun writeFreeTyvar(os, Types.ALPHA{level=level, eq=eq, ovld=ovld, ...}) =
      (TextIO.output1(os, #"{");
       writeInt(os, level);
       TextIO.output1(os, #" ");
       TextIO.output1(os, if eq then #"t" else #"f");
       TextIO.output1(os, #" ");
       (case ovld
	 of NONE => ()
	  | SOME tynames => writeList(os, fn(os, tyname, ()) => writeTyname(os, tyname), (), tynames));
       TextIO.output1(os, #"}"))

    fun writeTyvar(os, tyvar, alphaMap) =
      case tyvar
       of Types.RIGID s =>
	  (TextIO.output1(os, #"'"); writeIdent(os, s); alphaMap)
	| Types.FREE(Types.ALPHA{level=level, eq=eq, ovld=ovld, subst=subst}) =>
	  let val alpha = Types.ALPHA{level = level, eq=eq, ovld=ovld, subst=subst}
	      val (foundP, alphaMap, i) = findTyvar(alphaMap, alpha)
	      val _ = TextIO.output1(os, #"#")
	      val _ = writeInt(os, i)
	  in
	    if foundP then ()
	    else (TextIO.output1(os, #"="); writeFreeTyvar(os, alpha));
	    TextIO.output1(os, #" ");
	    alphaMap
	  end

    fun writeType(os, ty, alphaMap) =
      case Types.derefTy ty
       of Types.VAR tyvar => writeTyvar(os, tyvar, alphaMap)
	| Types.REC record => writeRecordTy(os, record, alphaMap)
	| Types.CONS(tys, tyname) => writeConsTy(os, tys, tyname, alphaMap)

    and writeRecordTy(os, record, alphaMap) =
      let val record = Types.derefRecord record
	  val Types.RECORD{fields = fields, subst = subst} = record
	  val fields = Types.sortFields fields
	  val _ = TextIO.output1(os, #"{")
	  val alphaMap = List.foldl (writeRecordTyField os) alphaMap fields
	  val _ = case subst
		   of SOME _ => TextIO.output1(os, #"?")
                    | NONE => ()
	  val _ = TextIO.output1(os, #"}")
      in
	alphaMap
      end

    and writeRecordTyField os ((label, ty), alphaMap) =
      let val _= TextIO.output1(os, #"{")
	  val _ = writeLabel(os, label)
	  val _ = TextIO.output1(os, #" ")
	  val alphaMap = writeType(os, ty, alphaMap)
	  val _ = TextIO.output1(os, #"}")
      in
	alphaMap
      end

    and writeConsTy(os, tys, tyname, alphaMap) =
      let val alphaMap = writeList(os, writeType, alphaMap, tys)
	  val _ = writeTyname(os, tyname)
      in
	alphaMap
      end

    fun readRigidTyvar is =
      Types.VAR(Types.RIGID(readIdent is))

    fun readAlpha is =
      let val _ = readChar(is, #"{")
	  val level = readInt is
	  val _ = readChar(is, #" ")
	  val eq =
	      case TextIO.input1 is
	       of SOME #"t" => true
		| SOME #"f" => false
		| SOME c => expected("t or f", c)
		| NONE => prematureEof "t or f"
	  val _ = readChar(is, #" ")
	  val ovld =
	      case TextIO.lookahead is
	       of SOME #"[" =>
		  let val (tynames, ()) = readList(is, fn(is, ()) => (readTyname is, ()), ())
		  in
		    SOME tynames
		  end
		| _ => NONE
	  val _ = readChar(is, #"}")
      in
	Types.ALPHA{level = level, eq = eq, ovld = ovld, subst = ref NONE}
      end

    fun readFreeTyvar(is, alphaMap) =
      let val index = readInt is
      in
	case TextIO.input1 is
	 of SOME #"=" =>
	    let val alpha = readAlpha is
		val _ = readChar(is, #" ")
	    in
	      (Types.VAR(Types.FREE alpha), updateAlphaMap(alphaMap, index, alpha))
	    end
	  | SOME #" " =>
	    let val alpha = valOf(findAlphaFromIndex(alphaMap, index))
	    in
	      (Types.VAR(Types.FREE alpha), alphaMap)
	    end
	  | SOME c => expected("= or space", c)
	  | NONE => prematureEof "= or space (after #<int> in <tyvar>"
      end

    fun readType(is, alphaMap) =
      case TextIO.input1 is
       of SOME #"'" => (readRigidTyvar is, alphaMap)
	| SOME #"#" => readFreeTyvar(is, alphaMap)
	| SOME #"{" => readRecordTy(is, alphaMap)
	| SOME #"<" => readConsTy(is, alphaMap)
	| SOME c => expected("<type>", c)
	| NONE => prematureEof "<type>"

    and readRecordTy(is, alphaMap) =
      let val _ = readChar(is, #"{")
	  val (fields, alphaMap) = readRecordTyFields(is, alphaMap)
	  val subst =
	      case TextIO.lookahead is
	       of SOME #"?" => (readChar(is, #"?"); SOME(ref NONE))
		| _ => NONE
	  val _ = readChar(is, #"}")
      in
	(Types.REC(Types.RECORD{fields = Types.sortFields fields, subst = subst}), alphaMap)
      end

    and readRecordTyFields(is, alphaMap) =
      let fun loop(acc, alphaMap) =
	    case TextIO.lookahead is
	     of SOME #"{" =>
		let val (field, alphaMap) = readRecordTyField(is, alphaMap)
		in
		  loop(field :: acc, alphaMap)
		end
	      | _ => (List.rev acc, alphaMap)
      in
	loop([], alphaMap)
      end

    and readRecordTyField(is, alphaMap) =
      let val _ = readChar(is, #"{")
	  val label = readLabel is
	  val _ = readChar(is, #" ")
	  val (ty, alphaMap) = readType(is, alphaMap)
	  val _ = readChar(is, #"}")
      in
	((label, ty), alphaMap)
      end

    and readConsTy(is, alphaMap) =
     let val (tys, alphaMap) = readList(is, readType, alphaMap)
	 val tyname = readTyname is
     in
       (Types.CONS(tys, tyname), alphaMap)
     end

    (* I/O of type functions *)

    fun writeTyfcn(os, tyfcn) =
      let fun mktyvar i = Types.RIGID(Int.toString i)
	  fun mkty i = Types.VAR(mktyvar i)
	  val arity = Types.tyfcnArity tyfcn
      in
	TextIO.output1(os, #"{");
	writeInt(os, arity);
	TextIO.output1(os, #" ");
	writeType(os, Types.applyTyfcn(tyfcn, List.tabulate(arity, mkty)), alphaMapEmpty);
	TextIO.output1(os, #"}")
      end

    fun readTyfcn is =
      let fun mktyvar i = Types.RIGID(Int.toString i)
	  val _ = readChar(is, #"{")
	  val arity = readInt is
	  val _ = readChar(is, #" ")
	  val (ty, alphaMap) = readType(is, alphaMapEmpty)
	  val _ = readChar(is, #"}")
      in
	(case alphaMap
	  of AM{next = 0, alist = []} => ()
	   | _ => raise Basis);
	Types.lambda(List.tabulate(arity, mktyvar), ty)
      end

    (* I/O of valenv *)

    fun writeValenvMapping(vid, idStatus, os) =
      (TextIO.output1(os, #"{");
       writeIdent(os, vid);
       TextIO.output1(os, #" ");
       writeIdStatus(os, idStatus);
       TextIO.output1(os, #"}");
       os)

    fun readValenvMapping(is, dict) =
      let val _ = readChar(is, #"{")
	  val vid = readIdent is
	  val _ = readChar(is, #" ")
	  val idStatus = readIdStatus is
	  val _ = readChar(is, #"}")
      in
	Dict.insert(dict, vid, idStatus)
      end

    fun writeValenv(os, VE dict) =
      writeDict(os, dict, writeValenvMapping)

    fun readValenv is =
      VE(readDict(is, readValenvMapping))

    (* I/O of tyenv *)

    fun writeTyenvMapping(tycon, TYSTR(tyfcn, valenv), os) =
      (TextIO.output1(os, #"{");
       writeIdent(os, tycon);
       TextIO.output1(os, #" ");
       writeTyfcn(os, tyfcn);
       TextIO.output1(os, #" ");
       writeValenv(os, valenv);
       TextIO.output1(os, #"}");
       os)

    fun readTyenvMapping(is, dict) =
      let val _ = readChar(is, #"{")
	  val tycon = readIdent is
	  val _ = readChar(is, #" ")
	  val tyfcn = readTyfcn is
	  val _ = readChar(is, #" ")
	  val valenv = readValenv is
	  val _ = readChar(is, #"}")
      in
	Dict.insert(dict, tycon, TYSTR(tyfcn, valenv))
      end

    fun writeTyenv(os, TE dict) =
      writeDict(os, dict, writeTyenvMapping)

    fun readTyenv is =
      TE(readDict(is, readTyenvMapping))

    (* I/O of env and strenv *)

    fun writeEnv(os, E(strenv, tyenv, valenv)) =
      (TextIO.output1(os, #"(");
       writeStrenv(os, strenv);
       writeTyenv(os, tyenv);
       writeValenv(os, valenv);
       TextIO.output1(os, #")"))

    and writeStrenv(os, SE dict) =
      writeDict(os, dict, writeStrenvMapping)

    and writeStrenvMapping(strid, env, os) =
      (TextIO.output1(os, #"{");
       writeIdent(os, strid);
       writeEnv(os, env);
       TextIO.output1(os, #"}");
       os)

    fun readEnv is =
      let val _ = readChar(is, #"(")
	  val strenv = readStrenv is
	  val tyenv = readTyenv is
	  val valenv = readValenv is
	  val _ = readChar(is, #")")
      in
	E(strenv, tyenv, valenv)
      end

    and readStrenv is =
      SE(readDict(is, readStrenvMapping))

    and readStrenvMapping(is, dict) =
      let val _ = readChar(is, #"{")
	  val strid = readIdent is
	  val env = readEnv is
	  val _ = readChar(is, #"}")
      in
	Dict.insert(dict, strid, env)
      end

    (* I/O of sigenv *)

    fun writeSigenvMapping(sigid, SIG env, os) =
      (TextIO.output1(os, #"{");
       writeIdent(os, sigid);
       writeEnv(os, env);
       TextIO.output1(os, #"}");
       os)

    fun readSigenvMapping(is, dict) =
      let val _ = readChar(is, #"{")
	  val sigid = readIdent is
	  val env = readEnv is
	  val _ = readChar(is, #"}")
      in
	Dict.insert(dict, sigid, SIG env)
      end

    fun writeSigenv(os, SIGE dict) =
      writeDict(os, dict, writeSigenvMapping)

    fun readSigenv is =
      SIGE(readDict(is, readSigenvMapping))

    (* I/O of basis *)

    fun writeBasis(os, BASIS(sigenv, env)) =
      (writeVersion os;
       TextIO.output1(os, #"(");
       writeSigenv(os, sigenv);
       writeEnv(os, env);
       TextIO.output1(os, #")"))

    fun readBasis is =
      let val _ = readVersion is
	  val _ = readChar(is, #"(")
	  val sigenv = readSigenv is
	  val env = readEnv is
	  val _ = readChar(is, #")")
	  val _ = readEof is
      in
	BASIS(sigenv, env)
      end

    fun write(file, basis) =
      let val os = TextIO.openOut file
      in
	Util.after(fn() => writeBasis(os, basis), fn() => TextIO.closeOut os)
      end

    fun read file =
      let val is = TextIO.openIn file
      in
	Util.after(fn() => readBasis is, fn() => TextIO.closeIn is)
      end

  end
