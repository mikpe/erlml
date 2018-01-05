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
structure Source : SOURCE =
  struct

    datatype source
      = SOURCE of
	  { fileName: string,
	    newLines: int list }	(* _descending_ order *)

    val dummy = SOURCE{fileName="", newLines=[]}

    (* The pos of an imaginary newline before a file's very
     * first character. This is necessary to adjust for the
     * weird notion of ML-Lex that the first character has
     * position 2. Not 0 or 1, but 2.
     * THIS WILL BREAK IF ML-LEX IS FIXED
     *)
    val startPos = 1

    fun lookup(newLines, pos) =
      let fun loop([], _) = {line = 1, column = pos - startPos}
	    | loop(newLine::newLines, line) =
		if pos > newLine then {line = line, column = pos - newLine}
		else loop(newLines, line - 1)
      in
	loop(newLines, 1 + List.length newLines)
      end

    fun sayErr s = TextIO.output(TextIO.stdErr, s)
    fun sayErr1 c = TextIO.output1(TextIO.stdErr, c)

    fun sayFile file = (sayErr file; sayErr1 #":")

    fun sayPos(newLines, pos) =
      let val {line,column} = lookup(newLines, pos)
      in
	sayErr(Int.toString line);
	sayErr1 #".";
	sayErr(Int.toString column)
      end

    fun sayMsg (SOURCE{fileName,newLines}) (msg,leftPos,rightPos) =
      (sayFile fileName;
       sayPos(newLines, leftPos);
       sayErr1 #"-";
       sayPos(newLines, rightPos);
       sayErr1 #" ";
       sayErr msg;
       sayErr1 #"\n")

  end (* structure Source *)
