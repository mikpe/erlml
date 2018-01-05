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
signature SOURCE =
  sig

    datatype source
      = SOURCE of
	  { fileName: string,
	    newLines: int list }	(* _descending_ order *)

    val startPos: int
    val dummy	: source
    val sayMsg	: source -> string * int * int -> unit

  end (* signature SOURCE *)
