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
structure Token : TOKEN =
  struct
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

    fun toString token =
      case token
        of ABSTYPE => "ABSTYPE"
         | AND => "AND"
         | ANDALSO => "ANDALSO"
         | AS => "AS"
         | CASE => "CASE"
         | DATATYPE => "DATATYPE"
         | DO => "DO"
         | ELSE => "ELSE"
         | END => "END"
         | EXCEPTION => "EXCEPTION"
         | FN => "FN"
         | FUN => "FUN"
         | HANDLE => "HANDLE"
         | IF => "IF"
         | IN => "IN"
         | INFIX => "INFIX"
         | INFIXR => "INFIXR"
         | LET => "LET"
         | LOCAL => "LOCAL"
         | NONFIX => "NONFIX"
         | OF => "OF"
         | OP => "OP"
	 | OPEN => "OPEN"
         | ORELSE => "ORELSE"
         | RAISE => "RAISE"
         | REC => "REC"
         | THEN => "THEN"
         | TYPE => "TYPE"
         | VAL => "VAL"
         | WITH => "WITH"
         | WITHTYPE => "WITHTYPE"
         | WHILE => "WHILE"
         | LPAREN => "LPAREN"
         | RPAREN => "RPAREN"
         | LBRACK => "LBRACK"
         | RBRACK => "RBRACK"
         | LBRACE => "LBRACE"
         | RBRACE => "RBRACE"
         | COMMA => "COMMA"
         | COLON => "COLON"
         | SEMICOLON => "SEMICOLON"
         | DOTDOTDOT => "DOTDOTDOT"
         | UNDERSCORE => "UNDERSCORE"
         | BAR => "BAR"
	 | EQ => "EQ"
         | FATARROW => "FATARROW"
         | THINARROW => "THINARROW"
         | HASH => "HASH"
	 | STAR => "STAR"
	 | DIGZ => "DIGZ"
	 | DIGNZ _ => "DIGNZ"
	 | NUMC _ => "NUMC"		(* TODO: convert attribute *)
         | INTC _ => "INTC"		(* TODO: convert attribute *)
         | WORDC _ => "WORDC"		(* TODO: convert attribute *)
         | REALC _ => "REALC"		(* TODO: convert attribute *)
         | STRINGC _ => "STRINGC"	(* TODO: convert attribute *)
         | CHARC _ => "CHARC"		(* TODO: convert attribute *)
         | ID _ => "ID _"		(* TODO: convert attribute *)
         | QUALID _ => "QUALID(_, _)"	(* TODO: convert attribute *)
         | TYVAR _ => "TYVAR _"		(* TODO: convert attribute *)
         | EQTYPE => "EQTYPE"
         | FUNCTOR => "FUNCTOR"
         | INCLUDE => "INCLUDE"
         | SHARING => "SHARING"
         | SIG => "SIG"
         | SIGNATURE => "SIGNATURE"
         | STRUCT => "STRUCT"
         | STRUCTURE => "STRUCTURE"
         | WHERE => "WHERE"
         | COLONGT => "COLONGT"
         | INFID _ => "INFID"		(* TODO: convert attribute *)
	 | ERROR => "ERROR"
         | EOF => "EOF"

  end
