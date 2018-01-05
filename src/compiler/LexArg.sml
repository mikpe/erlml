(*
 * Copyright 1997, 2015-2018 Mikael Pettersson
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
structure LexArg : LEXARG =
  struct

    type pos = int

    datatype lexarg
      = A of {	fileName	: string,
		instream	: TextIO.instream,
		newLines	: int list ref,
		thisLine	: pos ref,
		readPos		: int ref,
		unget		: (char * pos) option ref}

    fun new(fileName, instream) =
      let val pos = Source.startPos + 1
      in
	A{fileName = fileName,
	  instream = instream,
	  newLines = ref [],
	  thisLine = ref pos,
	  readPos = ref pos,
	  unget = ref NONE}
      end

    fun input1(A{instream, newLines, thisLine, readPos, unget, ...}) =
      case !unget
       of SOME(ch, pos) => (unget := NONE; (SOME ch, pos))
	| NONE =>
	  let val pos = !readPos
	      val chOpt =
		  case TextIO.input1 instream
		   of NONE => NONE
		    | SOME ch =>
		      let val incr =
			      case ch
			       of #"\n" =>
				  (newLines := pos :: !newLines;
				   thisLine := pos + 1;
				   1)
				| #"\t" =>
				  let val lpos = pos - !thisLine
				  in
				    8 - Int.rem(lpos, 8)
				  end
				| _ => 1
		      in
			readPos := pos + incr;
			SOME ch
		      end
	  in
	    (chOpt, pos)
	  end

    exception Unget

    fun unget1(A{unget, ...}, ch, pos) =
      case !unget
       of NONE => unget := SOME(ch, pos)
	| SOME _ => raise Unget

    fun source(A{fileName,newLines,...}) =
      Source.SOURCE{fileName = fileName, newLines = !newLines}

    fun error lexarg (msg,left,right) =
      Source.sayMsg (source lexarg) ("Error: "^msg, left, right)

  end (* structure LexArg *)
