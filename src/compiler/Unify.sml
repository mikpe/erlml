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
structure Unify : UNIFY =
  struct

    type Type = Types.Type

    exception Unify

    fun same_tyvars(Types.TYVAR{subst = subst1, ...}, Types.TYVAR{subst = subst2, ...}) = subst1 = subst2

    fun check_occur tyvar1 =
      let fun checkTy ty =
	    case Types.derefTy ty
	     of Types.VAR tyvar2 =>
		if same_tyvars(tyvar1, tyvar2) then raise Unify else ()
	      | Types.REC record =>
		let val Types.RECORD{fields, ...} = Types.derefRecord record
		in
		  List.app checkField fields
		end
	      | Types.CONS(tys, _) =>
		List.app checkTy tys
	  and checkField(_, ty) = checkTy ty
      in
	checkTy
      end

    fun check_level maxlevel =
      let fun checkTy ty =
	    case Types.derefTy ty
	     of Types.VAR(Types.TYVAR{level, eq, ovld, subst}) =>
		if level > maxlevel then subst := SOME(Types.VAR(Types.mkTyVar(maxlevel, eq, ovld)))
		else ()
	      | Types.REC record =>
		let val Types.RECORD{fields, ...} = Types.derefRecord record
		in
		  List.app checkField fields
		end
	      | Types.CONS(tys, _) =>
		List.app checkTy tys
	  and checkField(_, ty) = checkTy ty
      in
	checkTy
      end

    fun check_equality(eq, ty) =
      let fun checkTy ty =
	    case Types.derefTy ty
	     of Types.VAR(Types.TYVAR{level, eq, ovld, subst}) =>
		if eq then ()
		else subst := SOME(Types.VAR(Types.mkTyVar(level, true, ovld)))
	      | Types.REC record =>
		let val Types.RECORD{fields, is_flexible, ...} = Types.derefRecord record
		in
		  if is_flexible then raise Unify
		  else List.app checkField fields
		end
	      | Types.CONS(tys, tyname) =>
		if tyname = "->" then raise Unify
		else if tyname = "ref" then ()
		else List.app checkTy tys
	  and checkField(_, ty) = checkTy ty
      in
	if eq then checkTy ty else ()
      end

    fun check_ovld(NONE, _) = ()
      | check_ovld(SOME tynames, Types.CONS([], tyname)) =
	if Util.member(tyname, tynames) then () else raise Unify
      | check_ovld(SOME _, _) = raise Unify

    fun bind_tyvar(tyvar1 as Types.TYVAR{level, eq, ovld, subst}, ty2) =
      (check_occur tyvar1 ty2;
       check_level level ty2;
       check_equality(eq, ty2);
       check_ovld(ovld, ty2);
       subst := SOME ty2)

    fun join_level(level1, level2) = Util.min(level1, level2)

    fun join_eq(eq1, eq2) = eq1 orelse eq2

    fun join_ovld(NONE, ovld2) = ovld2
      | join_ovld(ovld1 as SOME _, NONE) = ovld1
      | join_ovld(SOME tynames1, SOME tynames2) = SOME(Util.intersect(tynames1, tynames2))

    fun unify_tyvars(tyvar1, tyvar2) =
      if same_tyvars(tyvar1, tyvar2) then ()
      else
	let val Types.TYVAR{level = level1, eq = eq1, ovld = ovld1, subst = subst1} = tyvar1
	    val Types.TYVAR{level = level2, eq = eq2, ovld = ovld2, subst = subst2} = tyvar2
	    val level3 = join_level(level1, level2)
	    val eq3 = join_eq(eq1, eq2)
	    val ovld3 = join_ovld(ovld1, ovld2)
	    val subst3 = SOME(Types.VAR(Types.mkTyVar(level3, eq3, ovld3)))
	in
	  subst1 := subst3;
	  subst2 := subst3
	end

    fun unify(ty1, ty2) = unify2(Types.derefTy ty1, Types.derefTy ty2)

    and unify2(Types.VAR tyvar1, Types.VAR tyvar2) = unify_tyvars(tyvar1, tyvar2)
      | unify2(Types.VAR tyvar1, ty2) = bind_tyvar(tyvar1, ty2)
      | unify2(ty1, Types.VAR tyvar2) = bind_tyvar(tyvar2, ty1)
      | unify2(Types.REC record1, Types.REC record2) = unify_records(Types.derefRecord record1, Types.derefRecord record2)
      | unify2(Types.CONS(tys1, tyname1), Types.CONS(tys2, tyname2)) =
	if tyname1 = tyname2 then unify_tys(tys1, tys2) else raise Unify
      | unify2(_, _) = raise Unify

   and unify_tys([], []) = ()
     | unify_tys(ty1 :: tys1, ty2 :: tys2) = (unify(ty1, ty2); unify_tys(tys1, tys2))
     | unify_tys(_, _) = raise Unify

   and unify_records(record1 as Types.RECORD{fields = fields1, is_flexible = is_flexible1, subst = subst1},
		     record2 as Types.RECORD{fields = fields2, is_flexible = is_flexible2, subst = subst2}) =
       if is_flexible1 then
	 (if is_flexible2 then
	    unify_records_unordered(fields1, fields2, subst1, subst2)
	  else
	    unify_records_less_or_equal(fields1, subst1, fields2, record2))
       else if is_flexible2 then
	 unify_records_less_or_equal(fields2, subst2, fields1, record1)
       else
	 unify_records_equal(fields1, fields2)

  end
