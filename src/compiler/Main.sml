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
structure Main : MAIN =
  struct

    fun sayErr s = TextIO.output(TextIO.stdErr, s)

    exception Main

    fun nyi msg =
      (sayErr("Main: nyi " ^ msg ^ "\n"); raise Main)

    exception Usage

    fun usage arg =
      let val progname = OS.Path.file(CommandLine.name())
      in
	sayErr(progname ^ ": invalid argument '" ^ arg ^ "'\n");
	sayErr("usage: " ^ progname ^ " [options] <file>.{sig,sml} ...\n");
	sayErr "valid options are:\n";
	sayErr "-v\n";
	raise Usage
      end

    fun version() = sayErr "ErlML version 0.0\n"

    fun option arg =
      case arg
       of "-v" => version()
	| _ => usage arg

    fun translate file =
      let val absynTopdec = Parser.parse_file file
	  val _ = Types.seedTynames file (* FIXME: CRC of file *)
	  val basis = TypeCheck.check absynTopdec
      in
	case absynTopdec
	 of Absyn.STRDECtopdec(Absyn.STRDEC[Absyn.STRUCTUREstrdec(Absyn.STRBIND[(strid, _)])]) =>
	    let val _ = Basis.write(strid ^ ".sml.basis", basis)
		val cerlModule = Translate.translate absynTopdec
	    in
	      CoreErlangPrint.printModule((OS.Path.base file) ^ ".core", cerlModule)
	    end
	  | Absyn.SIGDECtopdec(Absyn.SIGBIND[(sigid, _)]) =>
	    Basis.write(sigid ^ ".sig.basis", basis)
	  | _ => nyi "non-plain toplevel structure or signature file"
      end

    fun main argv =
      let fun loop([]) = OS.Process.success
	    | loop(arg :: argv) =
	      if String.sub(arg, 0) = #"-" then
		(option arg; loop argv)
	      else
		case OS.Path.ext arg
		 of SOME "sml" => (translate arg; loop argv)
		  | SOME "sig" => (translate arg; loop argv)
		  | _ => usage arg
      in
	loop argv
      end

  end
