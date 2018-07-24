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

    val tynameTUnit = ref ""
    val tynameCounter = ref 0

    fun seedTynames tunit = (tynameTUnit := tunit; tynameCounter := 0)

    fun mkTyname(tycon, arity, eq) =
      let val id = !tynameCounter
	  val _ = tynameCounter := id + 1
      in
	TYNAME{tunit = !tynameTUnit, id = id, tycon = tycon, arity = arity, eq = ref eq}
      end

    fun mkTyvar(level, eq, ovld) = FREE(ALPHA{level = level, eq = eq, ovld = ovld, subst = ref NONE})
    fun mkFreeTyvar(level) = mkTyvar(level, false, NONE)
    fun mkEqTyvar(level) = mkTyvar(level, true, NONE)
    fun mkOvldTyvar(ovld, level) = mkTyvar(level, false, SOME ovld)
    fun tyvarOvld(FREE(ALPHA{ovld, ...})) = ovld
      | tyvarOvld(RIGID _) = NONE

    (* tyvar dereference with path compression *)

    fun update(x, []) = x
      | update(x, subst :: substs) = (subst := SOME x; update(x, substs))

    local
      fun deref(VAR(FREE(ALPHA{subst as ref(SOME ty), ...})), subst', substs) = deref(ty, subst, subst' :: substs)
	| deref(ty, _, substs) = update(ty, substs)
    in
      fun derefTy(VAR(FREE(ALPHA{subst as ref(SOME ty), ...}))) = deref(ty, subst, [])
	| derefTy(ty) = ty
    end

    fun mkRecord(fields, is_flexible) = RECORD{fields = fields, subst = if is_flexible then SOME(ref NONE) else NONE}

    (* record dereference with path compression *)

    local
      fun deref(RECORD{subst = SOME(subst as ref(SOME record)), ...}, subst', substs) = deref(record, subst, subst' :: substs)
	| deref(record, _, substs) = update(record, substs)
    in
      fun derefRecord(RECORD{subst = SOME(subst as ref(SOME record)), ...}) = deref(record, subst, [])
	| derefRecord(record) = record
    end

    fun labelLt(INTlab i1, INTlab i2) = i1 < i2
      | labelLt(INTlab  _, IDlab   _) = true
      | labelLt(IDlab   _, INTlab  _) = false
      | labelLt(IDlab  n1, IDlab  n2) = n1 < n2

    fun fieldLt((l1, _), (l2, _)) = labelLt(l1, l2)

    fun sortFields fields = Util.sort(fieldLt, fields)

    fun tyAdmitsEq ty =
      let fun fold(_, eq, []) = eq
	    | fold(f, eq, x::xs) =
		case f x
		 of ALWAYS => fold(f, eq, xs)
		  | MAYBE => fold(f, MAYBE, xs)
		  | NEVER => NEVER
	  fun all(f, xs) = fold(f, ALWAYS, xs)
	  fun checkTy ty =
            case derefTy ty
	     of VAR(RIGID name) =>
		if String.sub(name, 0) = #"'" then ALWAYS else MAYBE
	      | VAR(FREE(ALPHA{level, eq, subst, ovld, ...})) =>
		(if eq then () else subst := SOME(VAR(mkTyvar(level, eq, ovld)));
		 ALWAYS)
	      | REC record =>
		let val RECORD{fields, subst} = derefRecord record
		in
		  case subst
		   of SOME _ => NEVER
		    | NONE => all(checkField, fields)
		end
	      | CONS(tys, TYNAME{eq, ...}) =>
		case !eq
		 of ALWAYS => ALWAYS
		  | MAYBE => all(checkTy, tys)
		  | NEVER => NEVER
	and checkField(_, ty) = checkTy ty
      in
        checkTy ty
      end

    fun tyIsClosed ty =
      case derefTy ty
       of VAR _ => false
	| REC record =>
	  let val RECORD{fields, subst} = derefRecord record
	  in
	    case subst
	     of SOME _ => false
	      | NONE => List.all (fn(_, ty) => tyIsClosed ty) fields
	  end
	| CONS(tys, _) => List.all tyIsClosed tys

    (* TYPE COMBINATORS: used internally to implement Type Functions and Type Schemes *)

    datatype tycomb
      = QUOTE of ty
      | ARG of int
      | MKREC of (label * tycomb) list * bool
      | MKCONS of tycomb list * tyname

    fun absBvars(bvars, ty) =
      let fun isQuote(QUOTE _) = true
	    | isQuote _ = false
	  fun abstract ty =
	    let val ty = derefTy ty
	    in
	      case ty
		of VAR alpha =>
		    let fun look([], _) = QUOTE ty
			  | look(tyvar::tyvars, i) =
			      if alpha = tyvar then ARG i else look(tyvars, i+1)
		    in
		      look(bvars, 0)
		    end
		 | REC record =>
		    let val RECORD{fields, subst} = derefRecord record
			fun abstractField(label, ty) = (label, abstract ty)
			val fields = map abstractField fields
			val is_flexible = case subst of NONE => false | SOME _ => true
			fun isFieldQuote(_, c) = isQuote c
		    in
		      if List.all isFieldQuote fields then QUOTE ty else MKREC(fields, is_flexible)
		    end
		 | CONS(tys, t) =>
		    let val cs = map abstract tys
		    in
		      if List.all isQuote cs then QUOTE ty else MKCONS(cs, t)
		    end
	    end
      in
	abstract ty
      end

    fun absAll ty =
      let fun scan(ty, alphas) =
	    case derefTy ty
	      of VAR alpha => if Util.member(alpha, alphas) then alphas else alpha :: alphas
	       | REC record =>
		 let fun scanField((_, ty), alphas) = scan(ty, alphas)
		     val RECORD{fields,...} = derefRecord record
		 in
		   List.foldl scanField alphas fields
		 end
	       | CONS(tys, _) => List.foldl scan alphas tys
	  val bvars = scan(ty, [])
      in
	(bvars, absBvars(bvars, ty))
      end

    fun absNone ty = QUOTE(derefTy ty)

    fun applyTycomb(comb, args) =
      let val args = Vector.fromList args
	  fun eval(QUOTE ty) = ty
	    | eval(ARG i) = Vector.sub(args, i)
	    | eval(MKREC(fields, is_flexible)) =
	      let fun evalField(label, c) = (label, eval c)
	      in
		REC(mkRecord(map evalField fields, is_flexible))
	      end
	    | eval(MKCONS(cs, t)) = CONS(map eval cs, t)
      in
	eval comb
      end

    (* TYPE FUNCTIONS *)

    datatype tyfcn = THETA of int * tycomb

    fun lambda(bvars, ty) = THETA(length bvars, absBvars(bvars, ty))

    fun tyfcnArity(THETA(arity, _)) = arity

    exception Types

    fun applyTyfcn(THETA(arity, comb), args) =
      if arity = length args then applyTycomb(comb, args)
      else raise Types

    fun tyfcnAdmitsEq(THETA(arity, comb)) =
      (* XXX: This conses a bit, but it's only called to check eqtype specs.
       * Perhaps there should be a TyComb.admitsEq?
       * The only requirement on mkeqty is that it return types
       * tau for who Ty.admitsEq(tau, true) returns true.
       *)
      let fun mkeqty _ = VAR(RIGID "'a")
	  val ty = applyTycomb(comb, List.tabulate(arity, mkeqty))
      in
	case tyAdmitsEq ty
	  of ALWAYS => true
	   | _ => false
      end

    (* TYPE SCHEMES *)

    datatype tyvarscheme = TVS of {eq: bool, ovld: tyname list option, name: string option}

    datatype tyscheme = TYS of {bvars: tyvarscheme list, comb: tycomb}

    (* GENERALIZATION *)

    fun gen_bvar(FREE(ALPHA{eq, ovld, ...}), _) = TVS{eq = eq, ovld = ovld, name = NONE}
      | gen_bvar(RIGID name, _) = TVS{eq = String.sub(name, 0) = #"'", ovld = NONE, name = SOME name}

    fun cannot_gen(_, NONE) = false
      | cannot_gen(RIGID _, SOME _) = true
      | cannot_gen(FREE(ALPHA{ovld = SOME _, ...}), SOME _) = true
      | cannot_gen(FREE(ALPHA{ovld = NONE, level, ...}), SOME limit) = level <= limit

    fun next_offset([]) = 0
      | next_offset((_, n) :: _) = n + 1

    fun gen_tyvar(tyvar, bvars_in, cond) =
      case cannot_gen(tyvar, cond)
        of true =>
	     (bvars_in, QUOTE(VAR tyvar))
        |  false =>
	     case Util.bound(bvars_in, tyvar)
               of SOME offset =>
		    (bvars_in, ARG offset)
		| NONE =>
		    let val offset = next_offset bvars_in
		    in
		      ((tyvar, offset) :: bvars_in, ARG offset)
		    end

    fun mkcons(combs, tyname) =
      let fun try_unquote([], tys) = QUOTE(CONS(List.rev tys, tyname))
	    | try_unquote(QUOTE ty :: combs', tys) = try_unquote(combs', ty :: tys)
	    | try_unquote(_ :: _, _) = MKCONS(combs, tyname)
      in
	try_unquote(combs, [])
      end

    fun mkrec(fields, subst) =
      let fun try_unquote([], fields'') = QUOTE(REC(RECORD{fields = List.rev fields'', subst = subst}))
	    | try_unquote((label, QUOTE ty) :: fields', fields'') = try_unquote(fields', (label, ty) :: fields'')
	    | try_unquote(_ :: _, _) = MKREC(fields, case subst of NONE => false |  SOME _ => true)
      in
	try_unquote(fields, [])
      end

    fun gen_ty(ty, bvars_in, cond) =
      case derefTy ty
       of VAR tyvar =>
	  gen_tyvar(tyvar, bvars_in, cond)
	| REC record =>
	  let val RECORD{fields, subst} = derefRecord record
	      val (bvars_out, fields', _) = List.foldl gen_field (bvars_in, [], cond) fields
	  in
	    (bvars_out, mkrec(List.rev fields', subst))
	  end
	| CONS(tys, tyname) =>
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
	(bvars_out, comb :: combs, cond)
      end

    fun gen_cond(ty, cond) =
      let val (bvars, comb) = gen_ty(ty, [], cond)
      in
	TYS{bvars = map gen_bvar (List.rev bvars), comb = comb}
      end

    fun genLimit(ty, limit) = gen_cond(ty, SOME limit)
    fun genAll ty = gen_cond(ty, NONE)
    fun genNone ty = TYS{bvars = [], comb = QUOTE ty}

    (* INSTANTIATION *)

    fun instFree(TYS{bvars, comb}, level) =
      let fun instBVar(TVS{eq, ovld, ...}) = mkTyvar(level, eq, ovld)
	  val bvars' = List.map instBVar bvars
      in
	(bvars', applyTycomb(comb, map VAR bvars'))
      end

    (* This is only used on (a) type schemes constructed with genNone,
     * and (b) type schemes constructed from explicit types with rigid
     * type variables in specifications. In case (a), there are no
     * type variables to instantiate, and in case (b), we reuse the
     * rigid type variables instead of consing up new ones.
     *)
    fun instRigid(TYS{bvars, comb}) =
      let fun instBVar(TVS{name = SOME name, ...}) = RIGID name
	    | instBVar _ = raise Types
	  val bvars' = List.map instBVar bvars
      in
        (bvars', applyTycomb(comb, map VAR bvars'))
      end

  end
