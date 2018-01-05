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

    type Level		= int
    type TyName		= string
    type Label		= string

    datatype Type	= VAR of TyVar
                        | REC of Record
			| CONS of Type list * TyName

    and TyVar		= TYVAR of {
			  (* generalization scope upper bound *)
			  level	: int,
			  (* requires equality? *)
			  eq	: bool,
			  (* optional monomorphic overloading *)
			  ovld	: TyName list option,
			  (* substitution *)
			  subst	: Type option ref
			  }

    and Record		= RECORD of {
			  (* known fields *)
			  fields : (Label * Type) list,
			  (* flexible? *)
			  is_flexible : bool,
			  (* substitution *)
			  subst : Record option ref
			  }

    val mkTyVar		: Level * bool * TyName list option -> TyVar
    val mkFreeTyVar	: Level -> TyVar
    val mkEqTyVar	: Level -> TyVar
    val mkOvldTyVar	: TyName list * Level -> TyVar

    val tyvarOvld	: TyVar -> TyName list option

    val derefTy		: Type -> Type

    val mkRecord	: (Label * Type) list * bool -> Record
    val derefRecord	: Record -> Record

  end
