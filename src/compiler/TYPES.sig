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
signature TYPES =
  sig

    (* TYPES *)

    type level		= int

    datatype label
      = IDlab of string
      | INTlab of int

    datatype tynameeq
      = NEVER
      | MAYBE
      | ALWAYS

    datatype tyname
      = TYNAME of {
	  tunit		: string,		(* FIXME: CRC of the source *)
	  id		: int,			(* unique per tunit *)
	  tycon		: string,
	  arity		: int,
	  eq		: tynameeq ref		(* admits equality? *)
	}

    datatype ty
      = VAR of tyvar
      | REC of record
      | CONS of ty list * tyname

    and tyvar
      = RIGID of string				(* without leading ' *)
      | FREE of alpha

    and alpha
      = ALPHA of {
	  level		: int,			(* generalization scope upper bound *)
	  eq		: bool,			(* admits/requires equality? *)
	  ovld		: tyname list option,	(* optional monomorphic overloading *)
	  subst		: ty option ref		(* substitution *)
        }

    and record
      = RECORD of {
	  fields	: (label * ty) list,		(* known fields *)
	  subst		: record option ref option	(* substitution, if flexible *)
	}

    val seedTynames	: string -> unit
    val mkTyname	: string * int * tynameeq -> tyname

    val mkTyvar		: level * bool * tyname list option -> tyvar
    val mkFreeTyvar	: level -> tyvar
    val mkEqTyvar	: level -> tyvar
    val mkOvldTyvar	: tyname list * level -> tyvar
    val tyvarOvld	: tyvar -> tyname list option

    val derefTy		: ty -> ty

    val mkRecord	: (label * ty) list * bool -> record
    val derefRecord	: record -> record
    val labelLt		: label * label -> bool
    val sortFields	: (label * ty) list -> (label * ty) list

    val tyAdmitsEq	: ty -> tynameeq

    (* TYPE FUNCTIONS *)

    type tyfcn
    val lambda		: tyvar list * ty -> tyfcn
    val tyfcnArity	: tyfcn -> int
    val applyTyfcn	: tyfcn * ty list -> ty
    val tyfcnAdmitsEq	: tyfcn -> bool

    (* TYPE SCHEMES *)

    type tyscheme
    val genLimit	: ty * level -> tyscheme
    val genAll		: ty -> tyscheme
    val genNone		: ty -> tyscheme
    val instFree	: tyscheme * level -> tyvar list * ty
    val instRigid	: tyscheme -> tyvar list * ty

  end
