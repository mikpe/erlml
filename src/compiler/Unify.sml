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

    type Type = Types.ty

    exception Unify

    fun same_tyvars(Types.FREE{subst = subst1, ...}, Types.FREE{subst = subst2, ...}) = subst1 = subst2
      | same_tyvars(Types.RIGID name1, Types.RIGID name2) = name1 = name2
      | same_tyvars(_, _) = false

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
	     of Types.VAR(Types.FREE{level, eq, ovld, subst}) =>
		if level > maxlevel then subst := SOME(Types.VAR(Types.mkTyvar(maxlevel, eq, ovld)))
		else ()
	      | Types.VAR(Types.RIGID _) => raise Unify (* FIXME *)
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

    fun check_equality(false, _) = ()
      | check_equality(true, ty) =
	if Types.tyAdmitsEq(ty, false) then () else raise Unify

    fun check_ovld(NONE, _) = ()
      | check_ovld(SOME tynames, Types.CONS([], tyname)) =
	if Util.member(tyname, tynames) then () else raise Unify
      | check_ovld(SOME _, _) = raise Unify

    fun bind_tyvar(Types.RIGID _, _) = raise Unify
      | bind_tyvar(tyvar1 as Types.FREE{level, eq, ovld, subst}, ty2) =
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

    fun unify_tyvars(Types.RIGID _, ty1, tyvar2, _) = bind_tyvar(tyvar2, ty1)
      | unify_tyvars(tyvar1, _, Types.RIGID _, ty2) = bind_tyvar(tyvar1, ty2)
      | unify_tyvars(Types.FREE{level = level1, eq = eq1, ovld = ovld1, subst = subst1}, _,
		     Types.FREE{level = level2, eq = eq2, ovld = ovld2, subst = subst2}, _) =
	let val level3 = join_level(level1, level2)
	    val eq3 = join_eq(eq1, eq2)
	    val ovld3 = join_ovld(ovld1, ovld2)
	    val subst3 = SOME(Types.VAR(Types.mkTyvar(level3, eq3, ovld3)))
	in
	  subst1 := subst3;
	  subst2 := subst3
	end

    fun unify(ty1, ty2) = unify2(Types.derefTy ty1, Types.derefTy ty2)

    and unify2(ty1 as Types.VAR tyvar1, ty2 as Types.VAR tyvar2) =
	if same_tyvars(tyvar1, tyvar2) then () else unify_tyvars(tyvar1, ty1, tyvar2, ty2)
      | unify2(Types.VAR tyvar1, ty2) = bind_tyvar(tyvar1, ty2)
      | unify2(ty1, Types.VAR tyvar2) = bind_tyvar(tyvar2, ty1)
      | unify2(Types.REC record1, Types.REC record2) = unify_records(record1, record2)
      | unify2(Types.CONS(tys1, tyname1), Types.CONS(tys2, tyname2)) =
	let fun tynameEq(tyname1, tyname2) =
	      (* Note that the eq attribute must be ignored, since the tyname
	       * from an abstract type spec may have a different eq attribute
	       * than the tyname from the implementation datbind. (FIXME: check)
	       *)
	      let val Types.TYNAME{strid = strid1, tycon = tycon1, ...} = tyname1
		  val Types.TYNAME{strid = strid2, tycon = tycon2, ...} = tyname2
	      in
		strid1 = strid2 andalso tycon1 = tycon2
	      end
	in
	  if tynameEq(tyname1, tyname2) then unify_tys(tys1, tys2) else raise Unify
	end
      | unify2(_, _) = raise Unify

   and unify_tys([], []) = ()
     | unify_tys(ty1 :: tys1, ty2 :: tys2) = (unify(ty1, ty2); unify_tys(tys1, tys2))
     | unify_tys(_, _) = raise Unify

   and unify_records(record1, record2) =
       let val record1 = Types.derefRecord record1
	   val record2 = Types.derefRecord record2
	   val Types.RECORD{fields = fields1, subst = subst1} = record1
	   val Types.RECORD{fields = fields2, subst = subst2} = record2
	   val fields1 = Types.sortFields fields1
	   val fields2 = Types.sortFields fields2
       in
	 case (subst1, subst2)
	  of (SOME ref1, SOME ref2) => unify_records_un(fields1, fields2, ref1, ref2, [])
	   | (SOME ref1, NONE) => unify_records_le(fields1, ref1, fields2, record2)
	   | (NONE, SOME ref2) => unify_records_le(fields2, ref2, fields1, record1)
	   | (NONE, NONE) => unify_records_eq(fields1, fields2)
       end

   and unify_records_un(fields1 as (field1 as (lab1, ty1)) :: fields1', fields2 as (field2 as (lab2, ty2)) :: fields2', ref1, ref2, fields3) =
       if lab1 = lab2 then (unify(ty1, ty2); unify_records_un(fields1', fields2', ref1, ref2, field1 :: fields3))
       else if Types.labelLt(lab1, lab2) then unify_records_un(fields1', fields2, ref1, ref2, field1 :: fields3)
       else unify_records_un(fields1, fields2', ref1, ref2, field2 :: fields3) (* lab1 > lab2 *)
     | unify_records_un(fields1, fields2, ref1, ref2, fields3) =
       let val fields3 = List.rev(List.revAppend(fields1, List.revAppend(fields2, fields3)))
	   val record3 = Types.mkRecord(fields3, true)
       in
	 ref1 := SOME record3;
	 ref2 := SOME record3
       end

   and unify_records_le([], ref1, _, record2) = ref1 := SOME record2
     | unify_records_le(_, _, [], _) = raise Unify
     | unify_records_le(fields1 as (lab1, ty1) :: fields1', ref1, (lab2, ty2) :: fields2, record2) =
       if lab1 = lab2 then (unify(ty1, ty2); unify_records_le(fields1', ref1, fields2, record2))
       else if Types.labelLt(lab1, lab2) then raise Unify
       else unify_records_le(fields1, ref1, fields2, record2) (* lab1 > lab2 *)

   and unify_records_eq([], []) = ()
     | unify_records_eq((lab1, ty1) :: fields1, (lab2, ty2) :: fields2) =
       if lab1 = lab2 then (unify(ty1, ty2); unify_records_eq(fields1, fields2))
       else raise Unify
     | unify_records_eq(_, _) = raise Unify

  end
