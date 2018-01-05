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
structure Types : TYPES =
  struct

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

    fun mkTyVar(level, eq, ovld) = TYVAR{level = level, eq = eq, ovld = ovld, subst = ref NONE}
    fun mkFreeTyVar(level) = mkTyVar(level, false, NONE)
    fun mkEqTyVar(level) = mkTyVar(level, true, NONE)
    fun mkOvldTyVar(ovld, level) = mkTyVar(level, false, SOME ovld)

    fun tyvarOvld(TYVAR{ovld, ...}) = ovld

    (* tyvar dereference with path compression *)

    fun update(x, []) = x
      | update(x, subst :: substs) = (subst := SOME x; update(x, substs))

    local
      fun deref(VAR(TYVAR{subst as ref(SOME ty), ...}), subst', substs) = deref(ty, subst, subst' :: substs)
	| deref(ty, _, substs) = update(ty, substs)
    in
      fun derefTy(VAR(TYVAR{subst as ref(SOME ty), ...})) = deref(ty, subst, [])
	| derefTy(ty) = ty
    end

    fun mkRecord(fields, is_flexible) = RECORD{fields = fields, is_flexible = is_flexible, subst = ref NONE}

    (* record dereference with path compression *)

    local
      fun deref(RECORD{subst as ref(SOME record), ...}, subst', substs) = deref(record, subst, subst' :: substs)
	| deref(record as RECORD{subst = ref NONE, ...}, _, substs) = update(record, substs)
    in
      fun derefRecord(RECORD{subst as ref(SOME record), ...}) = deref(record, subst, [])
	| derefRecord(record as RECORD{subst = ref NONE, ...}) = record
    end

  end
