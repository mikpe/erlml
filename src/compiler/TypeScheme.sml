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
structure TypeScheme : TYPE_SCHEME =
  struct
    type Level		= Types.Level
    type TyVar		= Types.TyVar
    type Type		= Types.Type

    datatype Comb	= QUOTE of Type
			| BOUND of int
			| REC of (Types.Label * Comb) list * bool * Types.Record option ref
			| CONS of Comb list * Types.TyName

    datatype TyVarScheme = TVS of {eq: bool, ovld: Types.TyName list option}

    datatype TypeScheme = TYS of {bvars: TyVarScheme list, comb: Comb}

    (* INSTANTIATION *)

    fun evalComb bvars =
      let fun eval(QUOTE ty) = ty
	    | eval(BOUND i) = Vector.sub(bvars, i)
	    | eval(REC(fields, is_flexible, subst)) =
	      let val fields' = List.map evalField fields
	      in
		Types.REC(Types.RECORD{fields = fields', is_flexible = is_flexible, subst = subst})
	      end
	    | eval(CONS(combs, tyname)) =
	      Types.CONS(List.map eval combs, tyname)
	  and evalField(label, comb) = (label, eval comb)
      in
	eval
      end

    fun instBVars(bvars, level) =
      let fun inst_bvar(TVS{eq, ovld}) = Types.mkTyVar(level, eq, ovld)
      in
	List.map inst_bvar bvars
      end

    fun inst(TYS{bvars, comb}, level) =
      let val bvars' = instBVars(bvars, level)
      in
	(bvars', evalComb (Vector.fromList(List.map Types.VAR bvars')) comb)
      end

    (* GENERALIZATION *)

    fun gen_bvar(Types.TYVAR{eq, ovld, ...}, _) = TVS{eq = eq, ovld = ovld}

    fun cannot_gen(_, NONE) = false
      | cannot_gen(Types.TYVAR{ovld = SOME _, ...}, SOME _) = true
      | cannot_gen(Types.TYVAR{ovld = NONE, level, ...}, SOME limit) = level <= limit

    fun next_offset([]) = 0
      | next_offset((_, n) :: _) = n + 1

    fun gen_tyvar(tyvar, bvars_in, cond) =
      case cannot_gen(tyvar, cond)
        of true =>
	     (bvars_in, QUOTE(Types.VAR tyvar))
        |  false =>
	     case Util.bound(bvars_in, tyvar)
               of SOME offset =>
		    (bvars_in, BOUND offset)
		| NONE =>
		    let val offset = next_offset bvars_in
		    in
		      ((tyvar, offset) :: bvars_in, BOUND offset)
		    end

    fun mkcons(combs, tyname) =
      let fun try_unquote([], tys) = QUOTE(Types.CONS(List.rev tys, tyname))
	    | try_unquote((QUOTE ty) :: combs', tys) = try_unquote(combs', ty :: tys)
	    | try_unquote(_ :: _, _) = CONS(combs, tyname)
      in
	try_unquote(combs, [])
      end

    fun mkrec(fields, is_flexible, subst) =
      let fun try_unquote([], fields'') = QUOTE(Types.REC(Types.RECORD{fields = fields'', is_flexible = is_flexible, subst = subst}))
	    | try_unquote((label, QUOTE ty) :: fields', fields'') = try_unquote(fields', (label, ty) :: fields'')
	    | try_unquote(_ :: _, _) = REC(fields, is_flexible, subst)
      in
	try_unquote(fields, [])
      end

    fun gen_ty(ty, bvars_in, cond) =
      case Types.derefTy ty
       of Types.VAR tyvar =>
	  gen_tyvar(tyvar, bvars_in, cond)
	| Types.REC record =>
	  let val Types.RECORD{fields, is_flexible, subst} = Types.derefRecord record
	      val (bvars_out, fields', _) = List.foldl gen_field (bvars_in, [], cond) fields
	  in
	    (bvars_out, mkrec(List.rev fields', is_flexible, subst))
	  end
	| Types.CONS(tys, tyname) =>
	  let val (bvars_out, combs, _) = List.foldl gen_elt (bvars_in, [], cond) tys
	  in
	    (bvars_out, mkcons(List.rev combs, tyname))
	  end

    and gen_field((label, ty), (bvars_in, fields, cond)) =
	let val (bvars_out, comb) = gen_ty(ty, bvars_in, cond)
	in
	  (bvars_out, (label, comb) :: fields, cond)
	end

    and gen_elt(ty, (bvars_in, combs, cond)) =
	let val (bvars_out, comb) = gen_ty(ty, bvars_in, cond)
	in
	  (bvars_out, comb::combs, cond)
	end

    fun gen_cond(ty, cond) =
      let val (bvars, comb) = gen_ty(ty, [], cond)
      in
	TYS{bvars = map gen_bvar (List.rev bvars), comb = comb}
      end

    fun gen_limit(ty, limit) = gen_cond(ty, SOME limit)
    fun gen_all ty = gen_cond(ty, NONE)
    fun gen_none ty = TYS{bvars = [], comb = QUOTE ty}

  end
