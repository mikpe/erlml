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

    datatype idstatus = CON of bool (* hasarg? *)
		      | EXN of bool (* hasarg? *)
		      | VAL
    datatype valenv   = VE of (ident, idstatus) Dict.dict (* TODO: add TypeScheme *)

    datatype env      = E of strenv * valenv (* TODO: add TyEnv *)
    and strenv        = SE of (ident, env) Dict.dict

    datatype sigma    = SIG of env (* TODO: add TyNameSet? *)
    datatype sigenv   = SIGE of (ident, sigma) Dict.dict

    datatype basis    = BASIS of sigenv * env (* TODO: add FunEnv *)

    val emptyEnv = E(SE(Dict.empty identCompare),
		     VE(Dict.empty identCompare))

    val emptyBasis = BASIS(SIGE(Dict.empty identCompare), emptyEnv)

    (* Initial Basis (TODO: incomplete) *)

    val veTextIO = VE(Dict.fromList(identCompare, [("output", VAL), ("stdOut", VAL)]))

    val initialSigEnv = SIGE(Dict.empty identCompare)
    val initialValEnv = VE(Dict.empty identCompare)
    val initialStrEnv = SE(Dict.fromList(identCompare, [("TextIO", E(SE(Dict.empty identCompare), veTextIO))]))
    val initialEnv = E(initialStrEnv, initialValEnv)
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

    (* I/O of env and strenv *)

    fun writeEnv(os, E(strenv, valenv)) =
      (TextIO.output1(os, #"(");
       writeStrenv(os, strenv);
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
	  val valenv = readValenv is
	  val _ = readChar(is, #")")
      in
	E(strenv, valenv)
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
