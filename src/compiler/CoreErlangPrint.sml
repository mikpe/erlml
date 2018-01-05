(*
 * Copyright 2017-2018 Mikael Pettersson
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
structure CoreErlangPrint : CORE_ERLANG_PRINT =
  struct

    fun prList(os, lparen, rparen, f, xs) =
      (TextIO.output1(os, lparen);
       (case xs
	 of (x::xs') =>
	    (f(os, x); List.app (fn(x) => (TextIO.output1(os, #","); f(os, x))) xs')
	  | [] => ());
       TextIO.output1(os, rparen))

    fun prAtom(os, a) = TextIO.output(os, CoreErlang.atomToString a)

    fun prLiteral(os, lit) =
      case lit
       of CoreErlang.L_ATOM a =>
	  prAtom(os, a)
	| CoreErlang.L_INTEGER i =>
	  TextIO.output(os, CoreErlang.integerToString i)
	| CoreErlang.L_FLOAT f =>
	  TextIO.output(os, CoreErlang.floatToString f)
	| CoreErlang.L_STRING s =>
	  TextIO.output(os, CoreErlang.stringToString s)
	| CoreErlang.L_NIL =>
	  TextIO.output(os, "[]")

    fun prConstant(os, cst) =
      case cst
       of CoreErlang.C_LITERAL lit =>
	  prLiteral(os, lit)
	| CoreErlang.C_CONS(c1, c2) =>
	  (* output lists as lists not right-recursive trees *)
	  let fun loop(CoreErlang.C_CONS(p1, p2)) =
		  (TextIO.output1(os, #",");
		   prConstant(os, c1);
		   loop c2)
		| loop(CoreErlang.C_LITERAL CoreErlang.L_NIL) =
		  TextIO.output1(os, #"]")
		| loop c =
		  (TextIO.output1(os, #"|");
		   prConstant(os, c);
		   TextIO.output1(os, #"]"))
	  in
	    TextIO.output1(os, #"[");
	    prConstant(os, c1);
	    loop c2
	  end
	| CoreErlang.C_TUPLE cs =>
	  prList(os, #"{", #"}", prConstant, cs)

    fun prVar(os, v) = TextIO.output(os, CoreErlang.varToString v)

    fun prPat(os, pat) =
      case pat
       of CoreErlang.P_LITERAL l =>
	  prLiteral(os, l)
	| CoreErlang.P_CONS(p1, p2) =>
	  (* output lists as lists not right-recursive trees *)
	  let fun loop(CoreErlang.P_CONS(p1, p2)) =
		  (TextIO.output1(os, #",");
		   prPat(os, p1);
		   loop p2)
		| loop(CoreErlang.P_LITERAL CoreErlang.L_NIL) =
		  TextIO.output1(os, #"]")
		| loop p =
		  (TextIO.output1(os, #"|");
		   prPat(os, p);
		   TextIO.output1(os, #"]"))
	  in
	    TextIO.output1(os, #"[");
	    prPat(os, p1);
	    loop p2
	  end
	| CoreErlang.P_TUPLE ps =>
	  prList(os, #"{", #"}", prPat, ps)
	| CoreErlang.P_VARIABLE v =>
	  prVar(os, v)
	| CoreErlang.P_ALIAS(v, p) =>
	  (prVar(os, v);
	   TextIO.output1(os, #"=");
	   prPat(os, p))

    fun prFName(os, CoreErlang.FNAME(name,arity)) =
      (prAtom(os, name);
       TextIO.output1(os, #"/");
       TextIO.output(os, Int.toString arity))

    fun prFVar(os, CoreErlang.FV v) = prVar(os, v)
      | prFVar(os, CoreErlang.FN n) = prFName(os, n)

    fun prExpr(os, expr) =
      case expr
       of CoreErlang.E_LITERAL l =>
	  prLiteral(os, l)
	| CoreErlang.E_CONS(e1, e2) =>
	  (* output lists as lists not right-recursive trees *)
	  let fun loop(CoreErlang.E_CONS(e1, e2)) =
		  (TextIO.output1(os, #",");
		   prExpr(os, e1);
		   loop e2)
		| loop(CoreErlang.E_LITERAL CoreErlang.L_NIL) =
		  TextIO.output1(os, #"]")
		| loop e =
		  (TextIO.output1(os, #"|");
		   prExpr(os, e);
		   TextIO.output1(os, #"]"))
	  in
	    TextIO.output1(os, #"[");
	    prExpr(os, e1);
	    loop e2
	  end
	| CoreErlang.E_TUPLE es =>
	  prList(os, #"{", #"}", prExpr, es)
	| CoreErlang.E_VARIABLE v =>
	  prVar(os, v)
	| CoreErlang.E_FNAME fname =>
	  prFName(os, fname)
        | CoreErlang.E_FUN fexpr =>
	  prFunExpr(os, fexpr)
	| CoreErlang.E_LET(v, e1, e2) =>
	  (TextIO.output(os, "let ");
	   prVar(os, v);
	   TextIO.output1(os, #"=");
	   prExpr(os, e1);
	   TextIO.output(os, " in ");
	   prExpr(os, e2))
	| CoreErlang.E_LETREC(fundefs, body) =>
	  (TextIO.output(os, "letrec ");
	   List.app (fn (fundef) => prFunDef(os, fundef)) fundefs;
	   TextIO.output(os, " in ");
	   prExpr(os, body))
	| CoreErlang.E_APPLY(fvar, es) =>
	  (TextIO.output(os, "apply ");
	   prFVar(os, fvar);
	   prList(os, #"(", #")", prExpr, es))
	| CoreErlang.E_CALL(m, f, es) =>
	  (TextIO.output(os, "call ");
	   prExpr(os, m);
	   TextIO.output1(os, #":");
	   prExpr(os, f);
	   prList(os, #"(", #")", prExpr, es))
	| CoreErlang.E_PRIMOP(a, es) =>
	  (TextIO.output(os, "primop ");
	   prAtom(os, a);
	   prList(os, #"(", #")", prExpr, es))
	| CoreErlang.E_CASE(e, cs) =>
	  (TextIO.output(os, "case ");
	   prExpr(os, e);
	   TextIO.output(os, " of ");
	   List.app (fn(p, e) => (prPat(os, p); TextIO.output(os, " when 'true' -> "); prExpr(os, e))) cs;
	   TextIO.output(os, " end"))
	| CoreErlang.E_TRY(e1, v1, e2, cv1, cv2, cv3, ce) =>
	  (TextIO.output(os, "try ");
	   prExpr(os, e1);
	   TextIO.output(os, " of ");
	   prVar(os, v1);
	   TextIO.output(os, " -> ");
	   prExpr(os, e2);
	   TextIO.output(os, " catch ");
	   prList(os, #"<", #">", prVar, [cv1, cv2, cv3]);
	   TextIO.output(os, " -> ");
	   prExpr(os, ce))

    and prFunExpr(os, CoreErlang.FUN(vs, e)) =
      (TextIO.output(os, "fun ");
       prList(os, #"(", #")", prVar, vs);
       TextIO.output(os, " -> ");
       prExpr(os, e))

    and prFunDef(os, (fname, fexpr)) =
      (prFName(os, fname);
       TextIO.output1(os, #"=");
       prFunExpr(os, fexpr))

    fun prExports(os, exports) =
      prList(os, #"[", #"]", prFName, exports)

    fun prAttribute(os, (atom, constant)) =
      (prAtom(os, atom);
       TextIO.output1(os, #"=");
       prConstant(os, constant))

    fun prAttributes(os, attributes) =
      (TextIO.output(os, "attributes ");
       prList(os, #"[", #"]", prAttribute, attributes))

    fun prModule(os, CoreErlang.MODULE(name,exports,attributes,fundefs)) =
      (TextIO.output(os, "module ");
       prAtom(os, name);
       TextIO.output1(os, #"\n");
       prExports(os, exports);
       TextIO.output1(os, #"\n");
       prAttributes(os, attributes);
       TextIO.output1(os, #"\n");
       List.app (fn fundef => (prFunDef(os, fundef); TextIO.output1(os, #"\n"))) fundefs;
       TextIO.output(os, "end\n"))

    fun printModule(file, module) =
      let val os = TextIO.openOut file
      in
	Util.after(fn() => prModule(os, module), fn() => TextIO.closeOut os)
      end

  end
