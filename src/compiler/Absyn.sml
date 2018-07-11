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
structure Absyn : ABSYN =
  struct

    type ident = Basis.ident

    datatype longid = datatype Basis.longid

    datatype label = datatype Basis.label

    (* Type Expressions *)

    type tyvar
      = ident

    type tycon
      = ident

    type longtycon
      = longid

    datatype ty
      = VARty of tyvar
      | RECty of (label * ty) list
      | CONSty of ty list * longtycon
      | FUNty of ty * ty

    (* Patterns *)

    type vid
      = ident

    type longvid
      = longid

    datatype scon
      = INTsc of IntInf.int
      | WORDsc of IntInf.int
      | REALsc of real
      | STRINGsc of string
      | CHARsc of char

    datatype pat
      = WILDpat
      | SCONpat of scon
      | VIDpat of longvid * Basis.idstatus option ref
      | RECpat of (label * pat) list * bool
      | CONSpat of longvid * pat
      | TYPEDpat of pat * ty
      | ASpat of vid * pat

    datatype typbind
      = TYPBIND of (tyvar list * tycon * ty) list

    datatype conbind
      = CONBIND of (vid * ty option) list

    datatype datbind
      = DATBIND of (tyvar list * tycon * conbind) list

    datatype exbind
      = CONexb of vid
      | OFexb of vid * ty
      | EQexb of vid * longvid

    datatype dec
      = DEC of dec1 list

    and dec1
      = VALdec of tyvar list ref * (pat * exp) list * (pat * match) list
      | TYPEdec of typbind
      | DATATYPEdec of datbind * typbind
      | DATAREPLdec of tycon * longtycon
      | ABSTYPEdec of datbind * typbind * dec
      | EXdec of exbind list
      | LOCALdec of dec * dec
      | OPENdec of longid list

    and exp
      = SCONexp of scon
      | VIDexp of longvid ref * Basis.idstatus option ref
      | RECexp of (label * exp) list
      | LETexp of dec * exp
      | APPexp of exp * exp
      | TYPEDexp of exp * ty
      | HANDLEexp of exp * match
      | RAISEexp of exp
      | FNexp of match

    and match
      = MATCH of (pat * exp) list

    type sigid
      = ident

    type strid
      = ident

    type longstrid
      = longid

    type funid
      = ident

    datatype spec
      = SPEC of spec1 list

    and spec1
      = VALspec of (ident * ty) list
      | TYPEspec of (tyvar list * tycon) list
      | EQTYPEspec of (tyvar list * tycon) list
      | DATATYPEspec of datbind
      | DATAREPLspec of tycon * longtycon
      | EXspec of conbind
      | STRUCTUREspec of (strid * sigexp) list
      | INCLUDEspec of sigexp
      | SHARINGTYspec of spec * longtycon list
      | SHARINGSTRspec of spec * longstrid list

    and sigexp
      = SPECsigexp of spec
      | SIGIDsigexp of sigid
      | WHEREsigexp of sigexp * tyvar list * longtycon * ty

    datatype sigbind
      = SIGBIND of (sigid * sigexp) list

    datatype strdec
      = STRDEC of strdec1 list

    and strdec1
      = DECstrdec of dec
      | STRUCTUREstrdec of strbind
      | LOCALstrdec of strdec * strdec

    and strbind
      = STRBIND of (strid * strexp) list

    and strexp
      = STRUCTstrexp of strdec
      | LONGSTRIDstrexp of longstrid
      | TRANSPARENTstrexp of strexp * sigexp * Basis.env option ref
      | OPAQUEstrexp of strexp * sigexp * Basis.env option ref
      | FUNAPPstrexp of funid * strexp
      | LETstrexp of strdec * strexp

    datatype funbind
      = FUNBIND of (funid * strid * sigexp * strexp) list

    datatype topdec
      = STRDECtopdec of strdec
      | SIGDECtopdec of sigbind
      | FUNDECtopdec of funbind

    val gensym =
	let val counter = ref 0
	in
	  fn () =>
	     let val c = 1 + !counter
	     in
	       counter := c;
	       Int.toString c
	     end
	end

  end
