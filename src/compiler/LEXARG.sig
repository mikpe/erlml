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
signature LEXARG =
  sig

    type pos = int
    type lexarg

    val new	: string * TextIO.instream -> lexarg
    val input1	: lexarg -> char option * pos
    exception	Unget
    val unget1	: lexarg * char * pos -> unit
    val error	: lexarg -> string * pos * pos -> unit
    val source	: lexarg -> Source.source

  end (* signature LEXARG *)
