(*
 * Copyright 2018 Mikael Pettersson
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
 *
 * This implements "4.6 Scope of Explicit Type Variables".
 *
 * Pass 1 recurses down the AST and computes, bottom-up, the set T of free
 * type variables in that AST, and a set U of pairs of valdecs and sets
 * of free type variables that occur unguarded at those valdecs.  As the
 * recursion returns up the AST, when a new free type variable is found and
 * added to T, the set U is updated by removing that type variable; any pair
 * whose set of type variables becomes empty is removed.  By construction,
 * T and U are disjoint.
 *
 * After pass 1, the set U contains the type variables implicitly scoped
 * at those valdecs.
 *
 * Pass 2 goes through the set U and annotates the valdecs with their
 * implicitly scoped type variables, via the ref cells in their AST nodes.
 *)
structure ExplicitTyVarScope : EXPLICIT_TYVAR_SCOPE =
  struct

    (* TyVar set ADT *)

    datatype tvs = TVS of (Absyn.tyvar, unit) Dict.dict

    val tvsEmpty = TVS(Dict.empty Basis.identCompare)

    fun tvsIsEmpty(TVS dict) = Dict.isEmpty dict

    fun tvsMember(TVS dict, alpha) =
      case Dict.find(dict, alpha)
	of NONE => false
	 | SOME _ => true

    fun tvsInsert(TVS dict, alpha) =
      TVS(Dict.insert(dict, alpha, ()))

    fun tvsDelete(TVS dict, alpha) =
      TVS(Dict.delete(dict, alpha))

    fun tvsUnion(TVS dict1, TVS dict2) =
      TVS(Dict.plus(dict1, dict2))

    fun tvsFold(f, init, TVS dict) =
      Dict.fold(fn(t, (), x) => f(t, x), init, dict)

    fun tvsToList tvs =
      tvsFold(op ::, [], tvs)

    fun tvsFromList list =
      List.foldl (fn(x, tvs) => tvsInsert(tvs, x)) tvsEmpty list

    fun pass1TyVar(tyvar, TU as (T, U)) =
      let fun unbind(RT as (tyvarseqRef, T), U) =
	    if tvsMember(T, tyvar) then
	      let val T' = tvsDelete(T, tyvar)
	      in
		if tvsIsEmpty T' then U
		else (tyvarseqRef, T') :: U
	      end
	    else RT :: U
      in
	if tvsMember(T, tyvar) then TU
	else
	  let val T' = tvsInsert(T, tyvar)
	      val U' = List.foldl unbind [] U
	  in
	    (T', U')
	  end
      end

    fun pass1Ty(ty, TU) =
      case ty
	of Absyn.VARty tyvar => pass1TyVar(tyvar, TU)
	 | Absyn.RECty tyrow => pass1TyRow(tyrow, TU)
	 | Absyn.CONSty(tys, _) => List.foldl pass1Ty TU tys
	 | Absyn.FUNty(ty1, ty2) => pass1Ty(ty2, pass1Ty(ty1, TU))

    and pass1TyRow(tyrow, TU) =
      List.foldl (fn((_, ty), TU) => pass1Ty(ty, TU)) TU tyrow

    fun pass1Pat(pat, TU) =
      case pat
	of Absyn.WILDpat => TU
	 | Absyn.SCONpat _ => TU
	 | Absyn.VIDpat _ => TU
	 | Absyn.RECpat(patrow, _) => pass1PatRow(patrow, TU)
	 | Absyn.CONSpat(_, pat) => pass1Pat(pat, TU)
	 | Absyn.TYPEDpat(pat, ty) => pass1Ty(ty, pass1Pat(pat, TU))
	 | Absyn.ASpat(_, pat) => pass1Pat(pat, TU)

    and pass1PatRow(patrow, TU) =
      List.foldl (fn((_, pat), TU) => pass1Pat(pat, TU)) TU patrow

    fun pass1ExBind(exbind, TU) =
      case exbind
        of Absyn.CONexb _ => TU
	 | Absyn.OFexb(_, ty) => pass1Ty(ty, TU)
	 | Absyn.EQexb _ => TU

    fun pass1Exp(exp, TU) =
      case exp
	of Absyn.SCONexp _ => TU
	 | Absyn.VIDexp _ => TU
	 | Absyn.RECexp exprow => pass1ExpRow(exprow, TU)
	 | Absyn.LETexp(dec, exp) => pass1Exp(exp, pass1Dec(dec, TU))
	 | Absyn.APPexp(exp1, exp2) => pass1Exp(exp2, pass1Exp(exp1, TU))
	 | Absyn.TYPEDexp(exp, ty) => pass1Ty(ty, pass1Exp(exp, TU))
	 | Absyn.HANDLEexp(exp, match) => pass1Match(match, pass1Exp(exp, TU))
	 | Absyn.RAISEexp exp => pass1Exp(exp, TU)
	 | Absyn.FNexp match => pass1Match(match, TU)

    and pass1ExpRow(exprow, TU) =
      List.foldl (fn((_, exp), TU) => pass1Exp(exp, TU)) TU exprow

    and pass1Recs(recs, TU) =
      List.foldl pass1Rec TU recs

    and pass1Rec((pat, match), TU) =
      pass1Match(match, pass1Pat(pat, TU))

    and pass1Match(Absyn.MATCH mrules, TU) =
      pass1Mrules(mrules, TU)

    and pass1Mrules(mrules, TU) =
      List.foldl pass1Mrule TU mrules

    and pass1Mrule((pat, exp), TU) =
      pass1Exp(exp, pass1Pat(pat, TU))

    and pass1Dec(Absyn.DEC decs, TU) =
      List.foldl pass1Dec1 TU decs

    and pass1Dec1(dec, TU) =
      case dec
        of Absyn.VALdec(tyvarseqRef, mrules, recs) => pass1ValDec(tyvarseqRef, mrules, recs, TU)
	 | Absyn.TYPEdec _ => TU
	 | Absyn.DATATYPEdec _ => TU
	 | Absyn.DATAREPLdec _ => TU
	 | Absyn.ABSTYPEdec(_, _, dec) => pass1Dec(dec, TU)
	 | Absyn.EXdec exbinds => List.foldl pass1ExBind TU exbinds
	 | Absyn.LOCALdec(dec1, dec2) => pass1Dec(dec2, pass1Dec(dec1, TU))
	 | Absyn.OPENdec _ => TU

    (* Annotate a 'valdec' that is nested inside another 'valdec' *)
    and pass1ValDec(tyvarseqRef, mrules, recs, (T1, U1)) =
      let val (T2, U2) = pass1Recs(recs, pass1Mrules(mrules, (tvsEmpty, [])))
	  val T2 = List.foldl (fn(t, T2) => tvsDelete(T2, t)) T2 (!tyvarseqRef)
      in
	if tvsIsEmpty T2 then (T1, U1)
	else (tvsUnion(T2, T1), (tyvarseqRef, T2) :: (U2 @ U1))
      end

    fun pass2(tyvarseqRef, T) =
      tyvarseqRef := tvsToList(tvsFold(fn(t, T') => tvsInsert(T', t), tvsFromList(!tyvarseqRef), T))

    (* Annotate a top-level 'valdec' *)
    fun annotateValDec(tyvarseqRef, mrules, recs) =
      let val (T, U) = pass1Recs(recs, pass1Mrules(mrules, (tvsEmpty, [])))
      in
	List.app pass2 ((tyvarseqRef, T) :: U)
      end

    (* Annotate 'dec' that is _not_ nested in 'valbind' *)
    fun annotateDec(Absyn.DEC decs) =
      List.app annotateDec1 decs

    and annotateDec1 dec =
      case dec
        of Absyn.VALdec(tyvarseqRef, mrules, recs) => annotateValDec(tyvarseqRef, mrules, recs)
	 | Absyn.TYPEdec _ => ()
	 | Absyn.DATATYPEdec _ => ()
	 | Absyn.DATAREPLdec _ => ()
	 | Absyn.ABSTYPEdec(_, _, dec) => annotateDec dec
	 | Absyn.EXdec _ => ()
	 | Absyn.LOCALdec(dec1, dec2) => (annotateDec dec1; annotateDec dec2)
	 | Absyn.OPENdec _ => ()

    fun annotateStrDec(Absyn.STRDEC strdecs) =
      List.app annotateStrDec1 strdecs

    and annotateStrDec1 strdec =
      case strdec
        of Absyn.DECstrdec dec => annotateDec dec
	 | Absyn.STRUCTUREstrdec strbind => annotateStrBind strbind
	 | Absyn.LOCALstrdec(strdec1, strdec2) => (annotateStrDec strdec1; annotateStrDec strdec2)

    and annotateStrBind(Absyn.STRBIND strbinds) =
      List.app annotateStrBind1 strbinds

    and annotateStrBind1(_, strexp) =
      annotateStrExp strexp

    and annotateStrExp strexp =
      case strexp
	of Absyn.STRUCTstrexp strdec => annotateStrDec strdec
	 | Absyn.LONGSTRIDstrexp _ => ()
	 | Absyn.TRANSPARENTstrexp(strexp, _, _) => annotateStrExp strexp
	 | Absyn.OPAQUEstrexp(strexp, _, _) => annotateStrExp strexp
	 | Absyn.FUNAPPstrexp(_, strexp) => annotateStrExp strexp
	 | Absyn.LETstrexp(strdec, strexp) => (annotateStrDec strdec; annotateStrExp strexp)

    fun annotateFunBind1(_, _, _, strexp) =
      annotateStrExp strexp

    fun annotateFunBind(Absyn.FUNBIND funbinds) =
      List.app annotateFunBind1 funbinds

    fun annotateTopDec topdec =
      case topdec
	of Absyn.STRDECtopdec strdec => annotateStrDec strdec
	 | Absyn.SIGDECtopdec _ => ()
	 | Absyn.FUNDECtopdec funbind => annotateFunBind funbind

    fun annotate topdec =
      annotateTopDec topdec

  end
