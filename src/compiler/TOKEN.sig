(*
 * Copyright 2015-2018 Mikael Pettersson
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
signature TOKEN =
  sig
    datatype token'	(* Core: reserved words *)
			= ABSTYPE
			| AND
			| ANDALSO
	   		| AS
	   		| CASE
			| DATATYPE
			| DO
			| ELSE
			| END
			| EXCEPTION
			| FN
			| FUN
			| HANDLE
			| IF
			| IN
			| INFIX
			| INFIXR
			| LET
			| LOCAL
			| NONFIX
			| OF
			| OP
			| OPEN
			| ORELSE
			| RAISE
			| REC
			| THEN
			| TYPE
			| VAL
			| WITH
			| WITHTYPE
			| WHILE
			(* Core: special symbols *)
			| LPAREN
			| RPAREN
			| LBRACK
			| RBRACK
			| LBRACE
			| RBRACE
			| COMMA
			| COLON
			| SEMICOLON
			| DOTDOTDOT
			| UNDERSCORE
			| BAR
			| EQ			(* may be used as ID *)
			| FATARROW
			| THINARROW
			| HASH
			| STAR			(* may be used as ID, except in TyCon *)
			(* Core: special constants *)
			| DIGZ			(* [0], admissible as fixity level or integer constant *)
			| DIGNZ of int		(* [1-9], admissible as fixity level, numeric label, or integer constant *)
			| NUMC of IntInf.int	(* [1-9][0-9]+, admissible as numeric label or integer constant *)
			| INTC of IntInf.int	(* integers starting with ~ or 0 *)
			| WORDC of IntInf.int
			| REALC of real
			| STRINGC of string
			| CHARC of char
			(* Core: identifiers *)
			| ID of string
			| QUALID of string list * string
			| TYVAR of string
			(* Modules *)
			| EQTYPE
			| FUNCTOR
			| INCLUDE
			| SHARING
			| SIG
			| SIGNATURE
			| STRUCT
			| STRUCTURE
			| WHERE
			| COLONGT
			(* Synthetic *)
			| INFID of string * int
			| ERROR
			| EOF

    type pos		= int
    datatype token	= T of pos * pos * token'

    val toString	: token' -> string
  end
