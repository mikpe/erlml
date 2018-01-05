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
 *
 * Recursive descent parser for SML'97:
 * - uses a token buffer with unbounded pushback capacity
 * - uses the shunting yard algorithm for infix expressions and patterns
 * - lowers all derived forms to the bare language, except for those that
 *   require semantic analysis (e.g. structure sharing constraints)
 *)
structure Parser : PARSER =
  struct

    fun sayErr s = TextIO.output(TextIO.stdErr, s)
    fun sayErr1 c = TextIO.output1(TextIO.stdErr, c)
    fun sayToken t = (sayErr(Token.toString t); sayErr1 #"\n")

    (*
     * Token buffer with unbounded pushback capacity.
     *
     * Some constructs require two tokens of lookahead (topdecs, tyvarseq).
     * While it is possible to handle them by combining a single-token pushback
     * buffer with rewriting affected parsing functions to return / pass around
     * a pre-read token, doing so greatly complicates the parser.  A buffer with
     * unbounded capacity is actually simpler than a single-token buffer.
     *)

    datatype tokens
      = TS of {lexarg : LexArg.lexarg,
	       lookahead : Token.token' list ref} (* XXX: tokens stripped of positions *)

    fun tokens_open lexarg = TS{lexarg = lexarg, lookahead = ref []}

    fun tokens_get(TS{lexarg, lookahead}) =
      case !lookahead
       of tok :: rest => (lookahead := rest; tok)
	| [] => let val Token.T(_, _, tok) = Lexer.lex lexarg in tok end (* XXX: preserve positions *)

    fun tokens_unget(TS{lookahead, ...}, tok) = lookahead := tok :: !lookahead

    fun lookingAt(msg, tokens) =
      let val tok = tokens_get tokens
	  val _ = tokens_unget(tokens, tok)
      in
	sayErr msg;
	sayErr ", tok ";
	sayToken tok
      end

    (*
     * Helpers for parsing single tokens.
     *
     * Token.token is not an equality type, due to Token.REALC having a real-typed attribute,
     * so we have specialized functions for all relevant cases.  A Token.eq predicate would
     * be awkward to implement and likely slower.
     *)

    val token_is_and = fn Token.AND => true | _ => false
    val token_is_bar = fn Token.BAR => true | _ => false
    val token_is_comma = fn Token.COMMA => true | _ => false
    val token_is_rbrace = fn Token.RBRACE => true | _ => false
    val token_is_rbrack = fn Token.RBRACK => true | _ => false
    val token_is_rparen = fn Token.RPAREN => true | _ => false
    val token_is_semicolon = fn Token.SEMICOLON => true | _ => false
    val token_is_thinarrow = fn Token.THINARROW => true | _ => false

    exception SyntaxError

    fun expected(msg, tok) =
      (sayErr "Syntax Error: expected "; sayErr msg; sayErr ", got "; sayToken tok; raise SyntaxError)

    fun check_end tok =
      case tok
       of Token.END => ()
	| _ => expected("END", tok)

    fun check_eq tok =
      case tok
       of Token.EQ => ()
	| _ => raise SyntaxError

    fun check_id tok =
      case tok
       of Token.ID id => id
	| _ => raise SyntaxError

    fun check_longid tok =
      case tok
       of Token.ID id => Absyn.LONGID([], id)
	| Token.QUALID(strids, id) => Absyn.LONGID(strids, id)
	| _ => raise SyntaxError

    fun check_rparen tok =
      case tok
       of Token.RPAREN => ()
	| _ => raise SyntaxError

    fun parse_label tokens =
      case tokens_get tokens
       of Token.ID id => Absyn.IDlab id
	| Token.STAR => Absyn.IDlab "*"
	| Token.DIGNZ n => Absyn.INTlab n
	| Token.NUMC n => Absyn.INTlab(IntInf.toInt n)
	| _ => raise SyntaxError

    fun parse_colon tokens =
      case tokens_get tokens
       of Token.COLON => ()
	| _ => raise SyntaxError

    fun parse_do tokens =
      case tokens_get tokens
       of Token.DO => ()
	| _ => raise SyntaxError

    fun parse_else tokens =
      case tokens_get tokens
       of Token.ELSE => ()
	| _ => raise SyntaxError

    fun parse_end tokens = check_end(tokens_get tokens)

    fun parse_eq tokens = check_eq(tokens_get tokens)

    fun parse_fatarrow tokens =
      case tokens_get tokens
       of Token.FATARROW => ()
	| _ => raise SyntaxError

    fun parse_fn tokens =
      case tokens_get tokens
       of Token.FN => ()
	| _ => raise SyntaxError

    fun parse_id tokens = check_id(tokens_get tokens)

    fun parse_in tokens =
      case tokens_get tokens
       of Token.IN => ()
	| _ => raise SyntaxError

    fun parse_lparen tokens =
      case tokens_get tokens
       of Token.LPAREN => ()
	| _ => raise SyntaxError

    fun parse_of tokens =
      case tokens_get tokens
       of Token.OF => ()
	| _ => raise SyntaxError

    fun parse_rbrace tokens =
      case tokens_get tokens
       of Token.RBRACE => ()
	| _ => raise SyntaxError

    fun parse_rparen tokens = check_rparen(tokens_get tokens)

    fun parse_then tokens =
      case tokens_get tokens
       of Token.THEN => ()
	| _ => raise SyntaxError

    fun parse_type tokens =
      case tokens_get tokens
       of Token.TYPE => ()
	| _ => raise SyntaxError

    fun parse_tyvar tokens =
      case tokens_get tokens
       of Token.TYVAR id => id
	| tok => expected("TYVAR", tok)

    fun parse_with tokens =
      case tokens_get tokens
       of Token.WITH => ()
	| _ => raise SyntaxError

    (*
     * Parse-time Fixity Environment
     *
     * The top-level environment has the following infix identifiers:
     *
     * infix  7  * / div mod
     * infix  6  + - ^
     * infixr 5  :: @
     * infix  4  = <> > >= < <=
     * infix  3  := o
     * infix  0  before
     *
     * We represent the precedence and associativity with a single integer
     * by incrementing the precedence level by one (range 1-10), and then
     * negating that if the identifier is right-associative.
     * An identifier that is unbound or bound to zero is considered nonfix.
     *)

    datatype fixenv = FE of (Absyn.ident, int) Dict.dict

    val fe_init =
	let val alist =
		[("/",	     8),
		 ("div",     8),
		 ("mod",     8),
		 ("*",	     8),
		 ("+",	     7),
		 ("-",	     7),
		 ("^",	     7),
		 ("::",	    ~6),
		 ("@",	    ~6),
		 ("=",	     5),
		 ("<>",	     5),
		 ("<",	     5),
		 (">",	     5),
		 ("<=",	     5),
		 (">=",	     5),
		 (":=",	     4),
		 ("o",	     4),
		 ("before",  1)]
	in
	  FE(Dict.fromList(Basis.identCompare, alist))
	end

    val fe_empty = FE(Dict.empty Basis.identCompare)

    fun fe_plus(FE dict1, FE dict2) = FE(Dict.plus(dict1, dict2))

    fun fe_insert(FE dict, id, prio) = FE(Dict.insert(dict, id, prio))

    fun id_is_infix(FE dict, id) =
      case Dict.find(dict, id)
       of NONE => NONE
	| SOME 0 => NONE
	| SOME prio => SOME(id, prio)

    fun token_is_infix(fe, eqok, tok) =
      case tok
       of Token.ID id => id_is_infix(fe, id)
	| Token.STAR => id_is_infix(fe, "*")
	| Token.EQ => if eqok then id_is_infix(fe, "=") else NONE
	| _ => NONE

    (*
     * A generic parser for infix patterns or expressions.
     *
     * This implements the shunting-yard algorithm, modified to keep
     * <operand,operator,priority> triplets on the stack and building
     * ASTs rather than emitting RPN code.  The result is essentially
     * a specialized shift-reduce parser.
     *)
    fun parse_infix(tokens, fe, eqok, parse_operand, combine, init) =
      let datatype 'a stack = S of 'a * Absyn.ident * int
	  fun right_binds_tighter(oprL, prioL, oprR, prioR) =
	    if oprL = oprR then prioL < 0	(* negative means right-associative *)
	    else abs prioR > abs prioL
	  fun finally([], opndR) = opndR
	    | finally(S(opndL, opr, _) :: stack, opndR) = finally(stack, combine(opr, opndL, opndR))
	  fun operand stack = operator(parse_operand(tokens, fe), stack)
	  and operator(opnd, stack) =
	      let val tok = tokens_get tokens
	      in
		case token_is_infix(fe, eqok, tok)
		 of SOME(id, prio) => resolve(id, prio, opnd, stack)
		  | NONE => (tokens_unget(tokens, tok); finally(stack, opnd))
	      end
	  and resolve(oprR, prioR, opndL, stack) =
	      case stack
	       of [] => operand(S(opndL, oprR, prioR) :: stack)
		| S(opndL', oprL, prioL) :: stack' =>
		  if right_binds_tighter(oprL, prioL, oprR, prioR) then operand(S(opndL, oprR, prioR) :: stack)
		  else resolve(oprR, prioR, combine(oprL, opndL', opndL), stack')
	  val stack =
	      case init
	       of NONE => []
		| SOME(opnd, opr, prio) => [S(opnd, opr, prio)]
      in
	operand stack
      end

    (*
     * Helper for parsing right-recursive constructs.
     *)

    fun rr_parse(tokens, parse_item, is_recur_token, combine) =
      let fun recur() =
	    let val left = parse_item tokens
		val tok = tokens_get tokens
	    in
	      if is_recur_token tok then combine(left, recur())
	      else (tokens_unget(tokens, tok); left)
	    end
      in
	recur()
      end

    (*
     * Helpers for parsing lists of items with separator tokens.
     *)

    (* Non-empty lists with given separator token.  *)
    fun item_plus_parse(tokens, parse_item, is_sep_token) =
      let fun loop acc =
	    let val item = parse_item tokens
		val acc = item :: acc
		val tok = tokens_get tokens
	    in
	      if is_sep_token tok then loop acc
	      else (tokens_unget(tokens, tok); List.rev acc)
	    end
      in
	loop []
      end

    (* Non-empty lists with comma as separator token.  Also consumes end token.  *)
    fun comma_item_plus_parse(tokens, parse_item, is_end_token) =
      let val items = item_plus_parse(tokens, parse_item, token_is_comma)
	  val tok = tokens_get tokens
      in
	if is_end_token tok then items
	else expected("${END}-token", tok)
      end

    (* Possibly empty lists with comma as separator token.  Also consumes end token.  *)
    fun comma_item_star_parse(tokens, parse_item, is_end_token) =
      let val tok = tokens_get tokens
      in
	if is_end_token tok then []
	else (tokens_unget(tokens, tok); comma_item_plus_parse(tokens, parse_item, is_end_token))
      end

    fun bar_item_plus_parse(tokens, parse_item) = item_plus_parse(tokens, parse_item, token_is_bar)

    fun and_item_plus_parse(tokens, parse_item) = item_plus_parse(tokens, parse_item, token_is_and)

    (*
     * Grammar: Type expressions
     *
     * ty	::= tyvar			(highest precedence)
     *		  | '{' <tyrow> '}'
     *		  | tyseq longtycon
     *		  | ty1 '*' ... '*' tyn		(n >= 2)
     *		  | ty '->' ty'			(right-associative)
     *		  | '(' ty ')'			(lowest precedence)
     * tyrow	::= lab ':' ty <',' tyrow>
     * tyseq	::= ty
     *		  |				(empty)
     *		  | '(' ty1 ',' ... ',' tyn ')'	(n >= 1)
     *)

    fun parse_ty tokens = parse_funty tokens

    and parse_funty tokens =
	rr_parse(tokens, parse_tuplety, token_is_thinarrow, Absyn.FUNty)

    and parse_tuplety tokens =
	let fun loop(acc, i) =
	      let val ty = parse_consty tokens
		  val acc = (Absyn.INTlab i, ty) :: acc
		  val i = i + 1
	      in
		case tokens_get tokens
		 of Token.STAR => loop(acc, i)
		  | tok =>
		    (tokens_unget(tokens, tok);
		     case acc
		      of [_] => ty
		       | _ => Absyn.RECty(List.rev acc))
	      end
	in
	  loop([], 1)
	end

    and parse_consty tokens =
	let fun loop tyseq =
	      case tokens_get tokens
	       of Token.ID id => loop [Absyn.CONSty(tyseq, Absyn.LONGID([], id))]
		(* Note that '*' is not a TyCon, so Token.STAR is excluded here *)
		| Token.QUALID(strids, id) => loop [Absyn.CONSty(tyseq, Absyn.LONGID(strids, id))]
		| tok =>
		  (tokens_unget(tokens, tok);
		   case tyseq
		    of [ty] => ty
		     | _ => raise SyntaxError)
	in
	  loop(parse_tyseq tokens)
	end

    and parse_tyseq tokens =
	case tokens_get tokens
	 of Token.TYVAR id => [Absyn.VARty id]
	  | Token.LBRACE =>
	    [Absyn.RECty(comma_item_star_parse(tokens, parse_tyrow_item, token_is_rbrace))]
	  | Token.LPAREN =>
	    comma_item_plus_parse(tokens, parse_ty, token_is_rparen)
	  | tok => (tokens_unget(tokens, tok); [])

    and parse_tyrow_item tokens =
	let val label = parse_label tokens
	    val _ = parse_colon tokens
	    val ty = parse_ty tokens
	in
	  (label, ty)
	end

    (*
     * Helpers to assemble expressions and patterns in the bare language.
     *)

    fun build_infix_pat(vid, pat1, pat2) =
      Absyn.CONSpat(Absyn.LONGID([], vid),
		    Absyn.RECpat([(Absyn.INTlab 1, pat1), (Absyn.INTlab 2, pat2)],
				 false))

    fun build_infix_exp(vid, exp1, exp2) =
      Absyn.APPexp(Absyn.VIDexp(Absyn.LONGID([], vid), ref NONE),
		   Absyn.RECexp([(Absyn.INTlab 1, exp1), (Absyn.INTlab 2, exp2)]))

    fun build_list([], _, xnil) = xnil
      | build_list(x :: xs, xcons, xnil) = xcons(x, build_list(xs, xcons, xnil))

    fun build_listpat pats =
      let val xcons = fn (pat1, pat2) => build_infix_pat("::", pat1, pat2)
	  val xnil = Absyn.VIDpat(Absyn.LONGID([], "nil"), ref NONE)
      in
	build_list(pats, xcons, xnil)
      end

    fun build_listexp exps =
      let val xcons = fn (exp1, exp2) => build_infix_exp("::", exp1, exp2)
	  val xnil = Absyn.VIDexp(Absyn.LONGID([], "nil"), ref NONE)
      in
	build_list(exps, xcons, xnil)
      end

    fun build_case_exp(exp, match) = Absyn.APPexp(Absyn.FNexp match, exp)

    fun mk_true_exp() = Absyn.VIDexp(Absyn.LONGID([], "true"), ref NONE)
    fun mk_false_exp() = Absyn.VIDexp(Absyn.LONGID([], "false"), ref NONE)

    fun build_if_exp(exp1, exp2, exp3) =
      let val match = Absyn.MATCH([(Absyn.VIDpat(Absyn.LONGID([], "true"), ref NONE), exp2),
				   (Absyn.VIDpat(Absyn.LONGID([], "false"), ref NONE), exp3)])
      in
	build_case_exp(exp1, match)
      end

    fun build_andalso(exp1, exp2) = build_if_exp(exp1, exp2, mk_false_exp())
    fun build_orelse(exp1, exp2) = build_if_exp(exp1, mk_true_exp(), exp2)

    fun build_seq_exp(exp1, exp2) = build_case_exp(exp1, Absyn.MATCH([(Absyn.WILDpat, exp2)]))

    fun build_while_exp(exp1, exp2) =
      let val vid = Absyn.LONGID([], Absyn.gensym())
	  val appvid = Absyn.APPexp(Absyn.VIDexp(vid, ref NONE), Absyn.RECexp [])
	  val exp = build_seq_exp(exp2, appvid)
	  val exp = build_if_exp(exp1, exp, Absyn.RECexp [])
	  val match = Absyn.MATCH([(Absyn.RECpat([], false), exp)])
      in
	Absyn.LETexp(Absyn.DEC [Absyn.VALdec([], [], [(Absyn.VIDpat(vid, ref NONE), match)])],
		     appvid)
      end

    fun build_hashexp lab =
      let val longid = Absyn.LONGID([], Absyn.gensym())
      in
	Absyn.FNexp(Absyn.MATCH([(Absyn.RECpat([(lab, Absyn.VIDpat(longid, ref NONE))], true), Absyn.VIDexp(longid, ref NONE))]))
      end

    (*
     * Helpers for identifier classification.
     *
     * Since "*" and "=" have specific uses in the syntax, they are returned from the
     * lexer as keyword tokens rather than as the general identifier token.
     *
     * In pattern contexts we map the "*" keyword to the corresponding identifier.
     *
     * In expression contexts we map the "*" and "=" keywords to their corresponding identifiers.
     *
     * In contexts that allow infix notation, identifiers that have infix status are mapped
     * to a synthetic token class representing infix identifiers.
     *)

    fun pat_filter_token tok =
      case tok
       of Token.STAR => Token.ID "*"
	(* Token.EQ is not mapped to Token.ID here *)
	| _ => tok

    fun parse_vid tokens = check_id(pat_filter_token(tokens_get tokens))

    fun exp_filter_token tok =
      case tok
       of Token.STAR => Token.ID "*"
	| Token.EQ => Token.ID "="
	| _ => tok

    fun fe_filter_token(fe, tok) =
      case tok
       of Token.ID id =>
	  (case id_is_infix(fe, id)
	    of NONE => tok
	     | SOME(_, prio) => Token.INFID(id, prio))
	| _ => tok

    fun pat_fe_filter_token(fe, tok) = fe_filter_token(fe, pat_filter_token tok)

    fun exp_fe_filter_token(fe, tok) = fe_filter_token(fe, exp_filter_token tok)

    fun parse_longvid_pat tokens = check_longid(pat_filter_token(tokens_get tokens))	(* includes STAR, excludes EQ *)

    fun parse_longvid_exp tokens = check_longid(exp_filter_token(tokens_get tokens))	(* includes STAR and EQ *)

    (*
     * Grammar: Patterns
     *
     * atpat	::= '_'
     *		  | scon
     *		  | <'op'>longvid
     *		  | '{' <patrow> '}'
     *		  | '(' pat1 ',' ... ',' patn ')'	(n >= 0)
     *		  | '[' pat1 ',' ... ',' patn ']'	(n >= 0)
     * patrow	::= '...'
     *		  | lab '=' pat <',' patrow>
     *		  | vid<':' ty> <'as' pat> <',' patrow>
     * apppat	::= atpat
     *		  | <'op'>longvid atpat
     * infpat	::= apppat
     *		  | infpat1 vid infpat2			(vid is infix)
     * pat	::= infpat				(highest precedence)
     *		  | pat ':' ty
     *		  | <'op'>vid<':' ty> 'as' pat		(lowest precedence)
     *
     * Note 1: The apppat and infpat layering is a correction from SuccessorML,
     * "Fixing various minor issues with the formal syntax".
     *
     * Implementation Note: The infix notation in fvalbind places very specific
     * requirements on the syntax of the formal parameters.  To handle this we
     * parse patterns in two steps: The first step parses following the grammar
     * and produces a representation of the actual parse tree.  The second step
     * maps the parse tree to an abstract syntax tree.  The intermediate parse
     * tree is inspected when parsing function clauses in fvalbinds; in other
     * contexts the parse tree is immediately mapped to a syntax tree.
     *)

    datatype pat
      (* pats: primitive forms, 1-to-1 with Absyn *)
      = WILDpat
      | SCONpat of Absyn.scon
      | RECpat of (Absyn.label * pat) list * bool	(* bool: flexible? *)
      | CONSpat of Absyn.longid * pat
      | TYPEDpat of pat * Absyn.ty
      | ASpat of Absyn.ident * pat
      (* pats: derived forms to be lowered or additional attributes to be removed *)
      | VIDpat of bool * Absyn.longid			(* bool: prefixed by op? *)
      | TUPLEpat of pat list
      | LISTpat of pat list
      | INFIXpat of Absyn.ident * pat * pat

    fun pat_to_absyn pat =
      case pat
       of WILDpat => Absyn.WILDpat
	| SCONpat sc => Absyn.SCONpat sc
	| RECpat(row, flexible) =>
	  let fun convert(lab, pat) = (lab, pat_to_absyn pat)
	  in
	    Absyn.RECpat(map convert row, flexible)
	  end
	| CONSpat(longid, pat) => Absyn.CONSpat(longid, pat_to_absyn pat)
	| TYPEDpat(pat, ty) => Absyn.TYPEDpat(pat_to_absyn pat, ty)
	| ASpat(vid, pat) => Absyn.ASpat(vid, pat_to_absyn pat)
	| VIDpat(_, longid) => Absyn.VIDpat(longid, ref NONE)
	| TUPLEpat pats =>
	  let fun loop([], [(_, pat)], _) = pat
		| loop([], row, _) = Absyn.RECpat(List.rev row, false)
		| loop(pat :: pats, row, i) = loop(pats, (Absyn.INTlab i, pat_to_absyn pat) :: row, i + 1)
	  in
	    loop(pats, [], 1)
	  end
	| LISTpat pats => build_listpat(map pat_to_absyn pats)
	| INFIXpat(opr, opndL, opndR) => build_infix_pat(opr, pat_to_absyn opndL, pat_to_absyn opndR)

    fun parse_atpat'(tokens, fe) =
      case parse_atpat_opt'(tokens, fe)
       of SOME pat => pat
	| NONE => raise SyntaxError

    and parse_atpat_opt'(tokens, fe) =
	let val tok = tokens_get tokens
	in
	  case pat_fe_filter_token(fe, tok)
	   of Token.UNDERSCORE => SOME WILDpat
	    | Token.DIGZ => SOME(SCONpat(Absyn.INTsc(IntInf.fromInt 0)))
	    | Token.DIGNZ n => SOME(SCONpat(Absyn.INTsc(IntInf.fromInt n)))
	    | Token.NUMC n => SOME(SCONpat(Absyn.INTsc n))
	    | Token.INTC n => SOME(SCONpat(Absyn.INTsc n))
	    | Token.WORDC n => SOME(SCONpat(Absyn.WORDsc n))
	    (* Token.REALC is disallowed here *)
	    | Token.STRINGC s => SOME(SCONpat(Absyn.STRINGsc s))
	    | Token.CHARC c => SOME(SCONpat(Absyn.CHARsc c))
	    | Token.OP => SOME(VIDpat(true, parse_longvid_pat tokens))
	    | Token.ID id => SOME(VIDpat(false, Absyn.LONGID([], id)))	(* includes STAR, excludes EQ, excludes infix IDs *)
	    | Token.QUALID(strids, id) => SOME(VIDpat(false, Absyn.LONGID(strids, id)))
	    | Token.LBRACE => SOME(parse_patrow'(tokens, fe))
	    | Token.LPAREN => SOME(parse_tuplepat'(tokens, fe))
	    | Token.LBRACK => SOME(parse_listpat'(tokens, fe))
	    | _ => (tokens_unget(tokens, tok); NONE)
	end

    and parse_patrow'(tokens, fe) =
	let fun loop acc =
	      case pat_filter_token(tokens_get tokens)
	       of Token.DOTDOTDOT => (parse_rbrace tokens; RECpat(List.rev acc, true))
		  | Token.DIGNZ n => row_eq(n, acc)
		  | Token.NUMC n => row_eq(IntInf.toInt n, acc)
		  | Token.ID id => row_id(id, acc)	(* includes STAR, excludes EQ *)
		  | _ => raise SyntaxError
	    and row_eq(n, acc) = (parse_eq tokens; row_pat(Absyn.INTlab n, acc))
	    and row_pat(lab, acc) =
		let val pat = parse_pat' fe tokens
		in
		  next((lab, pat) :: acc)
		end
	    and next acc = next_tok(tokens_get tokens, acc)
	    and next_tok(tok, acc) =
		(case tok
		  of Token.COMMA => loop acc
		   | Token.RBRACE => RECpat(List.rev acc, false)
		   | _ => raise SyntaxError)
	    and row_id(id, acc) =
		(case tokens_get tokens
		  of Token.EQ => row_pat(Absyn.IDlab id, acc)
		   | Token.COLON => row_ty(id, acc)
		   | Token.AS => row_as_pat(NONE, id, acc)
		   | tok =>
		     let val pat = VIDpat(false, Absyn.LONGID([], id))
			 val acc = (Absyn.IDlab id, pat) :: acc
		     in
		       next_tok(tok, acc)
		     end)
	    and row_ty(id, acc) =
		let val ty = parse_ty tokens
		in
		  case tokens_get tokens
		   of Token.AS => row_as_pat(SOME ty, id, acc)
		    | tok =>
		      let val pat = TYPEDpat(VIDpat(false, Absyn.LONGID([], id)), ty)
			  val acc = (Absyn.IDlab id, pat) :: acc
		      in
			next_tok(tok, acc)
		      end
		end
	    and row_as_pat(tyOpt, id, acc) =
		let val pat = parse_pat' fe tokens
		    val pat = ASpat(id, pat)
		    val pat = case tyOpt
			       of NONE => pat
				| SOME ty => TYPEDpat(pat, ty)
		    val acc = (Absyn.IDlab id, pat) :: acc
		in
		  next acc
		end
	in
	  case tokens_get tokens
	   of Token.RBRACE => RECpat([], false)
	    | tok => (tokens_unget(tokens, tok); loop [])
	end

    and parse_tuplepat'(tokens, fe) =
	TUPLEpat(comma_item_star_parse(tokens, parse_pat' fe, token_is_rparen))

    and parse_listpat'(tokens, fe) =
	LISTpat(comma_item_star_parse(tokens, parse_pat' fe, token_is_rbrack))

    and parse_apppat'(tokens, fe) =
	let val tok = tokens_get tokens
	in
	  case pat_fe_filter_token(fe, tok)
	   of Token.OP => parse_apppat_atpat_opt'(true, parse_longvid_pat tokens, tokens, fe)
	    | Token.ID id =>	(* includes STAR, excludes EQ, excludes infix IDs *)
	      parse_apppat_atpat_opt'(false, Absyn.LONGID([], id), tokens, fe)
	    | Token.QUALID(strids, id) => parse_apppat_atpat_opt'(false, Absyn.LONGID(strids, id), tokens, fe)
	    | _ => (tokens_unget(tokens, tok); parse_atpat'(tokens, fe))
	end

    and parse_apppat_atpat_opt'(have_op, longid, tokens, fe) =
	case parse_atpat_opt'(tokens, fe)
	 of SOME pat => CONSpat(longid, pat)
	  | NONE => VIDpat(have_op, longid)

    and parse_infpat'(tokens, fe) = parse_infpat3'(tokens, fe, NONE)

    and parse_infpat3'(tokens, fe, init) =
	parse_infix(tokens, fe, false, parse_apppat', INFIXpat, init)

    and parse_pat' fe tokens =
	let val tok = tokens_get tokens
	in
	  case pat_fe_filter_token(fe, tok)
	   of Token.OP => parse_pat_after_vid'(true, parse_vid tokens, tokens, fe)	(* includes STAR, excludes EQ *)
	    | Token.ID id => parse_pat_after_vid'(false, id, tokens, fe)		(* includes STAR, excludes EQ, excludes infix IDs *)
	    | _ =>
	      let val _ = tokens_unget(tokens, tok)
		  val pat = parse_infpat'(tokens, fe)
	      in
		case tokens_get tokens
		 of Token.COLON => TYPEDpat(pat, parse_ty tokens)
		  | tok => (tokens_unget(tokens, tok); pat)
	      end
	end

    and parse_pat_after_vid'(have_op, id, tokens, fe) =
	case tokens_get tokens
	 of Token.COLON =>
	    let val ty = parse_ty tokens
	    in
	      case tokens_get tokens
	       of Token.AS =>
		  let val pat = parse_pat' fe tokens
		  in
		    TYPEDpat(ASpat(id, pat), ty)
		  end
		| tok => (tokens_unget(tokens, tok); TYPEDpat(VIDpat(have_op, Absyn.LONGID([], id)), ty))
	    end
	  | Token.AS =>
	    let val pat = parse_pat' fe tokens
	    in
	      ASpat(id, pat)
	    end
	  | tok =>
	    let val _ = tokens_unget(tokens, tok)
		val apppat = parse_apppat_atpat_opt'(have_op, Absyn.LONGID([], id), tokens, fe)
		val tok = tokens_get tokens
	    in
	      case pat_fe_filter_token(fe, tok)
	       of Token.INFID(id, prio) => parse_infpat3'(tokens, fe, SOME(apppat, id, prio))
		| _ => (tokens_unget(tokens, tok); apppat)
	    end

    fun parse_atpat(tokens, fe) = pat_to_absyn(parse_atpat'(tokens, fe))
    fun parse_pat(tokens, fe) = pat_to_absyn(parse_pat' fe tokens)

    (*
     * Parse and resolve function clause parameter syntax.
     * A function clause can have one of the following three forms:
     *
     * 1. <op>vid atpat1 ... atpatn <:ty> = exp				(n >= 1)
     * 2. (atpat1 vid atpat2) atpat3 ... atpatn <:ty> = exp		(n >= 2, vid is infix)
     * 3. atpat1 vid atpat2 <:ty> = exp					(vid is infix)
     *
     * XXX: merge parse & resolve into a single state machine for improved error reporting?
     *)

    datatype farg	(* not "funarg" since historically that has a different meaning *)
      = INFIDfarg of Absyn.ident
      | ATPATfarg of pat

    fun parse_fargs(tokens, fe) =
      let fun loop acc =
	    let val tok = tokens_get tokens
	    in
	      case pat_fe_filter_token(fe, tok)
	       of Token.INFID(id, _) => loop(INFIDfarg id :: acc)
		| Token.COLON => (tokens_unget(tokens, tok); List.rev acc)
		| Token.EQ => (tokens_unget(tokens, tok); List.rev acc)
		| _ => (tokens_unget(tokens, tok); loop(ATPATfarg(parse_atpat'(tokens, fe)) :: acc))
	    end
      in
	loop []
      end

    fun resolve_fargs fargs =
      let fun farg2pat(ATPATfarg pat) = pat
	    | farg2pat(INFIDfarg _) = raise SyntaxError
	  fun finish(id, pats) =
	    let val arity = length pats
		val pat = pat_to_absyn(TUPLEpat pats)
	    in
	      (id, arity, pat)
	    end
      in
	case fargs
	 of [ATPATfarg pat1, INFIDfarg id, ATPATfarg pat2] =>		(* form #3 *)
	    (id, 1, pat_to_absyn(TUPLEpat[pat1, pat2]))
	  | ATPATfarg(TUPLEpat[INFIXpat(id, pat1, pat2)]) :: rest =>	(* form #2 *)
	    finish(id, TUPLEpat[pat1, pat2] :: map farg2pat rest)
	  | ATPATfarg(VIDpat(_, Absyn.LONGID([], id))) :: rest =>	(* form #1 *)
	    finish(id, map farg2pat rest)
	  | _ => raise SyntaxError
      end

    fun build_fdef fclauses =
      let fun mkvids(0, vids, [(_, exp)]) = (vids, exp)
	    | mkvids(0, vids, row) = (vids, Absyn.RECexp row)
	    | mkvids(i, vids, row) =
	      let val vid = Absyn.gensym()
	      in
		mkvids(i - 1, vid :: vids, (Absyn.INTlab i, Absyn.VIDexp(Absyn.LONGID([], vid), ref NONE)) :: row)
	      end
	  fun mkfn([], exp) = exp
	    | mkfn(vid :: vids, exp) = Absyn.FNexp(Absyn.MATCH([(Absyn.VIDpat(Absyn.LONGID([], vid), ref NONE), mkfn(vids, exp))]))
	  fun mkmatch(vid :: vids, exp) = Absyn.MATCH([(Absyn.VIDpat(Absyn.LONGID([], vid), ref NONE), mkfn(vids, exp))])
	    | mkmatch([], _) = raise SyntaxError
	  fun mkfdef(name, arity, mrules) =
	    let val match = Absyn.MATCH mrules
		val (vids, exp) = mkvids(arity, [], [])
		val exp = Absyn.APPexp(Absyn.FNexp match, exp)
		val match = mkmatch(vids, exp)
	    in
	      (Absyn.VIDpat(Absyn.LONGID([], name), ref NONE), match)
	    end
	  fun check(fclauses, name, arity, mrules) =
	    case fclauses
	     of [] => mkfdef(name, arity, List.rev mrules)
	      | (name', arity', mrule') :: fclauses' =>
		if name = name' andalso arity = arity' then check(fclauses', name, arity, mrule' :: mrules)
		else raise SyntaxError
      in
	case fclauses
	 of (name, arity, mrule) :: fclauses' => check(fclauses', name, arity, [mrule])
	  | [] => raise SyntaxError
      end

    (*
     * Grammar: Declarations (Core)
     *
     * dec	::= 'val' tyvarseq valbind
     *		  | 'fun' tyvarseq fvalbind
     *		  | 'type' typbind
     *		  | 'datatype' datbind <'withtype' typbind>
     *		  | 'datatype' tycon '=' 'datatype' longtycon
     *		  | 'abstype' datbind <'withtype' typbind> 'with' dec 'end'
     *		  | 'exception' exbind
     *		  | 'local' dec1 'in' dec2 'end'
     *		  | 'open' longstrid1 ... longstridn		(n >= 1)
     *		  |						(empty)
     *		  | dec1 <';'> dec2
     *		  | infix <d> vid1 ... vidn			(n >= 1)
     *		  | infixr <d> vid1 ... vidn			(n >= 1)
     *		  | noinfix vid1 ... vidn			(n >= 1)
     * valbind	::= pat '=' exp <'and' valbind>
     *		  | 'rec' valbind				(Note 1)
     * fvalbind	::= fclause <'and' fvalbind>
     * fdef	::= fclause <'|' fclause>
     * fclause	::= <'op'>vid atpat1...atpatn <':' ty> '=' exp	(Note 2, 3)
     * typbind	::= tyvarseq tycon '=' ty <'and' typbind>
     * datbind	::= tyvarseq tycon '=' conbind <'and' datbind>
     * conbind	::= <'op'>vid <'of' ty> <'|' conbind>
     * exbind	::= <'op'>vid <'of' ty> <'and' exbind>
     *		  | <'op'>vid '=' <'op'>longvid <'and' exbind>
     *
     * Note 1: For each value binding "pat = exp" within "rec", "exp" must be of
     * the form "fn match".
     *
     * Note 2: If "vid" has infix status, then either "op" must be present, or
     * "vid" must be infixed as "(atpat1 vid atpat2) ..."; the parentheses may
     * be dropped if n = 2, i.e. if ": ty" or "= exp" follows immediately.
     *)

    fun parse_op_opt_vid(tokens, fe) =
      let val tok = tokens_get tokens
      in
	case pat_fe_filter_token(fe, tok)
	 of Token.OP => parse_vid tokens
	  | Token.ID id => id
	  | _ => raise SyntaxError
      end

    fun parse_op_opt_longvid(tokens, fe) =
      let val tok = tokens_get tokens
      in
	case pat_fe_filter_token(fe, tok)
	 of Token.OP => parse_longvid_pat tokens
	  | Token.ID id => Absyn.LONGID([], id)
	  | Token.QUALID(strids, id) => Absyn.LONGID(strids, id)
	  | _ => raise SyntaxError
      end

    fun parse_exbind_item fe tokens =
      let val id = parse_op_opt_vid(tokens, fe)
      in
	case tokens_get tokens
	 of Token.OF => Absyn.OFexb(id, parse_ty tokens)
	  | Token.EQ => Absyn.EQexb(id, parse_op_opt_longvid(tokens, fe))
	  | tok => (tokens_unget(tokens, tok); Absyn.CONexb id)
      end

    fun parse_exbind(tokens, fe) =
      and_item_plus_parse(tokens, parse_exbind_item fe)

    fun parse_exception_dec(tokens, fe) = Absyn.EXdec(parse_exbind(tokens, fe))

    fun parse_ofty_opt tokens =
      case tokens_get tokens
       of Token.OF => SOME(parse_ty tokens)
	| tok => (tokens_unget(tokens, tok); NONE)

    fun parse_conbind_item fe tokens =
      let val id = parse_op_opt_vid(tokens, fe)
	  val tyOpt = parse_ofty_opt tokens
      in
	(id, tyOpt)
      end

    fun parse_conbind(tokens, fe) =
      Absyn.CONBIND(bar_item_plus_parse(tokens, parse_conbind_item fe))

    (* <tyvarseq> may be followed by <pat> in <valbind> or <fclause>, so after seeing "("
     * we must inspect one more token to determine if the "(" is part of the <tyvarseq> or
     * not.  Therefore this requires two tokens of lookahead.
     *)
    fun parse_tyvarseq tokens =
      case tokens_get tokens
       of Token.TYVAR id => [id]
	| (tok as Token.LPAREN) =>
	  (case tokens_get tokens
	    of Token.TYVAR id =>
	       (case tokens_get tokens
		 of Token.RPAREN => [id]
		  | Token.COMMA => id :: comma_item_plus_parse(tokens, parse_tyvar, token_is_rparen)
		  | _ => raise SyntaxError)
	     | tok2 => (tokens_unget(tokens, tok2); tokens_unget(tokens, tok); []))
	| tok => (tokens_unget(tokens, tok); [])

    val parse_tycon = parse_id	(* excludes STAR *)

    fun parse_tyvarseq_tycon tokens =
      let val tyvarseq = parse_tyvarseq tokens
	  val tycon = parse_tycon tokens
      in
	(tyvarseq, tycon)
      end

    fun parse_tyvarseq_tycon_eq tokens =
      let val (tyvarseq, tycon) = parse_tyvarseq_tycon tokens
	  val _ = parse_eq tokens
      in
	(tyvarseq, tycon)
      end

    fun parse_tyvarseq_tycon_eq_ty tokens =
      let val (tyvarseq, tycon) = parse_tyvarseq_tycon_eq tokens
	  val ty = parse_ty tokens
      in
	(tyvarseq, tycon, ty)
      end

    fun parse_typbind tokens =
      Absyn.TYPBIND(and_item_plus_parse(tokens, parse_tyvarseq_tycon_eq_ty))

    fun parse_type_dec tokens = Absyn.TYPEdec(parse_typbind tokens)

    fun parse_datbind_item fe tokens =
      let val (tyvarseq, tycon) = parse_tyvarseq_tycon_eq tokens
	  val conbind = parse_conbind(tokens, fe)
      in
	(tyvarseq, tycon, conbind)
      end

    fun parse_datbind(datbOpt, tokens, fe) =
      let fun parse() = and_item_plus_parse(tokens, parse_datbind_item fe)
	  val datbinds =
	      case datbOpt
	       of NONE => parse()
		| SOME datb =>
		  case tokens_get tokens
		   of Token.AND => datb :: parse()
		    | tok => (tokens_unget(tokens, tok); [datb])
      in
	Absyn.DATBIND datbinds
      end

    fun parse_withtype_opt tokens =
      case tokens_get tokens
       of Token.WITHTYPE => parse_typbind tokens
	| tok => (tokens_unget(tokens, tok); Absyn.TYPBIND [])

    (* XXX: check that it's not QUALID(strids, "*") *)
    fun parse_longtycon tokens = check_longid(tokens_get tokens)

    fun parse_datatype_dec(tokens, fe) =
      let fun do_datbind datbOpt =
	    let val datbind = parse_datbind(datbOpt, tokens, fe)
		val typbind = parse_withtype_opt tokens
	    in
	      Absyn.DATATYPEdec(datbind, typbind)
	    end
      in
	case tokens_get tokens
	 of Token.ID tycon =>
	    let val _ = parse_eq tokens
	    in
	      case tokens_get tokens
	       of Token.DATATYPE => Absyn.DATAREPLdec(tycon, parse_longtycon tokens)
		| tok =>
		  (* We've seen "datatype tycon = X" where X isn't "datatype",
		   * so we must have a conbind and possibly more datbinds.
		   * If our token pushback buffer was larger we could just
		   * push back "X", "=", and "tycon" and retry at datbind.
		   * Instead we parse the first datbind, and make parse_datbind
		   * accept an optional pre-parsed datbind.
		   *
		   * XXX: rewrite to use new unbounded pushback buffer
		   *)
		  let val _ = tokens_unget(tokens, tok)
		      val conbind = parse_conbind(tokens, fe)
		      val datb = ([], tycon, conbind)
		  in
		    do_datbind(SOME datb)
		  end
	    end
	  | tok => (tokens_unget(tokens, tok); do_datbind NONE)
      end

    fun is_strid id = Char.isAlpha(String.sub(id, 0))

    fun check_strid id = if is_strid id then () else raise SyntaxError

    fun parse_longstrid tokens =
      let val (longstrid as Absyn.LONGID(_, strid)) = parse_longtycon tokens
	  val _ = check_strid strid
      in
	longstrid
      end

    fun parse_open_longstrids tokens =
      let fun loop acc =
	    let fun check(strids, id) = (check_strid id; loop(Absyn.LONGID(strids, id) :: acc))
	    in
	      case tokens_get tokens
	       of Token.ID id => check([], id)
		| Token.QUALID(strids, id) => check(strids, id)
		| tok => (tokens_unget(tokens, tok); List.rev acc)
	    end
      in
	loop [parse_longstrid tokens]
      end

    fun parse_open_dec tokens = Absyn.OPENdec(parse_open_longstrids tokens)

    fun parse_fixity_vids tokens =
      let fun loop acc =
	    let val tok = tokens_get tokens
	    in
	      case pat_filter_token tok
	       of Token.ID id => loop(id :: acc)
		| _ => (tokens_unget(tokens, tok); List.rev acc)
	    end
      in
	loop [parse_vid tokens]
      end

    fun parse_infix_directive tokens =
      let val d =
	      case tokens_get tokens
	       of Token.DIGNZ d => d
		| tok => (tokens_unget(tokens, tok); 0)
      in
	(d, parse_fixity_vids tokens)
      end

    fun process_fixity_directive(prio, vids) =
      List.foldl (fn(id, fe) => fe_insert(fe, id, prio)) fe_empty vids

    fun parse_infix_dec tokens =
      let val (d, vids) = parse_infix_directive tokens
	  val prio = d + 1
      in
	process_fixity_directive(prio, vids)
      end

    fun parse_infixr_dec tokens =
      let val (d, vids) = parse_infix_directive tokens
	  val prio = ~(d + 1)
      in
	process_fixity_directive(prio, vids)
      end

    fun parse_nonfix_dec tokens =
      let val vids = parse_fixity_vids tokens
	  val prio = 0
      in
	process_fixity_directive(prio, vids)
      end

    (* Declarations parsing needs to be greedy, except when parsing top-level
     * declarations at the REPL, in which case we should stop at the first SEMI.
     *
     * We pass in an inherited fixity environment to be used for parsing, and
     * return a synthesized fixity environment containing only the additions
     * from this declaration, if any.  Sequencing combines these appropriately.
     * For LOCAL dec1 IN dec2 END, the synthesized bindings from dec1 are merged
     * with the initial inherited bindings to be the inherited bindings for dec2,
     * whose synthesized bindings become the overall synthesized bindings.
     *)
    fun parse_dec(tokens, feIn, stopAtSemi) =
      let fun outer(acc, feIn, feOut) =
	    let fun done() = (Absyn.DEC(List.rev acc), feOut)
		fun onlydec dec = outer(dec :: acc, feIn, feOut)
		fun fixity feOut' = outer(acc, fe_plus(feIn, feOut'), fe_plus(feOut, feOut'))
		fun both(dec, feOut') = outer(dec :: acc, fe_plus(feIn, feOut'), fe_plus(feOut, feOut'))
	    in
	      case tokens_get tokens
	       of Token.VAL => onlydec(parse_val_dec(tokens, feIn))
		| Token.FUN => onlydec(parse_fun_dec(tokens, feIn))
		| Token.TYPE => onlydec(parse_type_dec tokens)
		| Token.DATATYPE => onlydec(parse_datatype_dec(tokens, feIn))
		| Token.ABSTYPE => both(parse_abstype_dec(tokens, feIn))
		| Token.EXCEPTION => onlydec(parse_exception_dec(tokens, feIn))
		| Token.LOCAL => both(parse_local_dec(tokens, feIn))
		| Token.OPEN => onlydec(parse_open_dec tokens)
		| Token.INFIX => fixity(parse_infix_dec tokens)
		| Token.INFIXR => fixity(parse_infixr_dec tokens)
		| Token.NONFIX => fixity(parse_nonfix_dec tokens)
		| Token.SEMICOLON => if stopAtSemi then done() else outer(acc, feIn, feOut)
		| tok => (tokens_unget(tokens, tok); done())
	    end
      in
	outer([], feIn, fe_empty)
      end

    and parse_abstype_dec(tokens, feIn) =
	let val datbind = parse_datbind(NONE, tokens, feIn)
	    val typbind = parse_withtype_opt tokens
	    val _ = parse_with tokens
	    val (dec, feOut) = parse_dec(tokens, feIn, false)
	    val _ = parse_end tokens
	in
	  (Absyn.ABSTYPEdec(datbind, typbind, dec), feOut)
	end

    and parse_local_dec(tokens, feIn) =
	let val (dec1, feOut1) = parse_dec(tokens, feIn, false)
	    val _ = parse_in tokens
	    val (dec2, feOut2) = parse_dec(tokens, fe_plus(feIn, feOut1), false)
	    val _ = parse_end tokens
	in
	  (Absyn.LOCALdec(dec1, dec2), feOut2)
	end

    and parse_val_dec(tokens, fe) =
	let val tyvarseq = parse_tyvarseq tokens
	    fun done(nonrecs, recs) = Absyn.VALdec(tyvarseq, nonrecs, recs)
	    fun dorec(nonrecs, recs) =
	      done(nonrecs, and_item_plus_parse(tokens, parse_valrec_item fe))
	    fun nonrec acc =
	      case tokens_get tokens
	       of Token.REC => dorec(List.rev acc, [])
		| tok =>
		  let val _ = tokens_unget(tokens, tok)
		      val pat = parse_pat(tokens, fe)
		      val _ = parse_eq tokens
		      val exp = parse_exp fe tokens
		      val acc = (pat, exp) :: acc
		  in
		    case tokens_get tokens
		     of Token.AND => nonrec acc
		      | tok => (tokens_unget(tokens, tok); done(acc, []))
		  end
	in
	  nonrec []
	end

    and parse_valrec_item fe tokens =
	let val pat = parse_pat(tokens, fe)
	    val _ = parse_eq tokens
	    val _ = parse_fn tokens
	    val match = parse_match(tokens, fe)
	in
	  (pat, match)
	end

    and parse_fun_dec(tokens, fe) =
	let val tyvarseq = parse_tyvarseq tokens
	in
	  Absyn.VALdec(tyvarseq, [], and_item_plus_parse(tokens, parse_fdef fe))
	end

    and parse_fdef fe tokens =
	build_fdef(bar_item_plus_parse(tokens, parse_fclause fe))

    and parse_fclause fe tokens =
	let val (name, arity, pat) = resolve_fargs(parse_fargs(tokens, fe))
	    val tyOpt =
		case tokens_get tokens
		 of Token.COLON => SOME(parse_ty tokens)
		  | tok => (tokens_unget(tokens, tok); NONE)
	    val _ = parse_eq tokens
	    val exp = parse_exp fe tokens
	    val exp =
		case tyOpt
		 of SOME ty => Absyn.TYPEDexp(exp, ty)
		  | NONE => exp
	    val mrule = (pat, exp)
	in
	  (name, arity, mrule)
	end

    (*
     * Grammar: Expressions
     *
     * atexp	::= scon
     *		  | <'op'>longvid
     *		  | '{' <exprow> '}'
     *		  | '#' lab
     *		  | '(' exp1 ',' ... ',' expn ')'		(n >= 0)
     *		  | '[' exp1 ',' ... ',' expn ']'		(n >= 0)
     *		  | '(' exp1 ';' ... ';' expn ')'		(n >= 2)
     *		  | 'let' dec 'in' exp1 ';' ... ',' expn 'end'	(n >= 1)
     * exprow	::= lab '=' exp <',' exprow>
     * appexp	::= atexp
     *		  | appexp atexp
     * infexp	::= appexp
     *		  | infexp1 vid infexp2				(vid is infix)
     * exp	::= infexp					(highest precendence)
     *		  | exp ':' ty
     *		  | exp1 'andalso' exp2
     *		  | exp1 'orelse' exp2
     *		  | exp 'handle' match
     *		  | 'raise' exp
     *		  | 'if' exp1 'then' exp2 'else' exp3
     *		  | 'while' exp1 'do' exp2
     *		  | 'case' exp 'of' match
     *		  | 'fn' match					(lowest precedence)
     * match	::= mrule <'|' match>
     * mrule	::= pat '=>' exp
     *)

    and parse_atexp(tokens, fe) =
      case parse_atexp_opt(tokens, fe)
       of SOME exp => exp
	| NONE => raise SyntaxError

    and parse_atexp_opt(tokens, fe) =
	let val tok = tokens_get tokens
	in
	  case exp_fe_filter_token(fe, tok)
	   of Token.DIGZ => SOME(Absyn.SCONexp(Absyn.INTsc(IntInf.fromInt 0)))
	    | Token.DIGNZ n => SOME(Absyn.SCONexp(Absyn.INTsc(IntInf.fromInt n)))
	    | Token.NUMC n => SOME(Absyn.SCONexp(Absyn.INTsc n))
	    | Token.INTC n => SOME(Absyn.SCONexp(Absyn.INTsc n))
	    | Token.WORDC n => SOME(Absyn.SCONexp(Absyn.WORDsc n))
	    | Token.REALC r => SOME(Absyn.SCONexp(Absyn.REALsc r))
	    | Token.STRINGC s => SOME(Absyn.SCONexp(Absyn.STRINGsc s))
	    | Token.CHARC c => SOME(Absyn.SCONexp(Absyn.CHARsc c))
	    | Token.OP => SOME(Absyn.VIDexp(parse_longvid_exp tokens, ref NONE))
	    | Token.ID id => SOME(Absyn.VIDexp(Absyn.LONGID([], id), ref NONE))	(* includes STAR and EQ, excludes infix IDs *)
	    | Token.QUALID(strids, id) => SOME(Absyn.VIDexp(Absyn.LONGID(strids, id), ref NONE))
	    | Token.LBRACE => SOME(parse_exprow(tokens, fe))
	    | Token.LPAREN => SOME(parse_lparen_exp(tokens, fe))
	    | Token.LBRACK => SOME(parse_listexp(tokens, fe))
	    | Token.LET => SOME(parse_letexp(tokens, fe))
	    | Token.HASH => SOME(parse_hashexp tokens)
	    | _ => (tokens_unget(tokens, tok); NONE)
	end

    and parse_exprow(tokens, fe) =
	Absyn.RECexp(comma_item_star_parse(tokens, parse_exprow_item fe, token_is_rbrace))

    and parse_exprow_item fe tokens =
	let val lab = parse_label tokens
	    val _ = parse_eq tokens
	    val exp = parse_exp fe tokens
	in
	  (lab, exp)
	end

    and parse_lparen_exp(tokens, fe) =
	let fun tuple(acc, i) =
	      let val exp = parse_exp fe tokens
		  val acc = (Absyn.INTlab i, exp) :: acc
		  val i = i + 1
	      in
		case tokens_get tokens
		 of Token.COMMA => tuple(acc, i)
		  | Token.RPAREN => Absyn.RECexp(List.rev acc)
		  | _ => raise SyntaxError
	      end
	in
	  case tokens_get tokens
	   of Token.RPAREN => Absyn.RECexp []
	    | tok =>
	      let val _ = tokens_unget(tokens, tok)
		  val exp = parse_exp fe tokens
	      in
		case tokens_get tokens
		 of Token.RPAREN => exp
		  | Token.COMMA => tuple([(Absyn.INTlab 1, exp)], 2)
		  | Token.SEMICOLON =>
		    let val exp2 = parse_sequence_exp(tokens, fe)
			val _ = parse_rparen tokens
		    in
		      build_seq_exp(exp, exp2)
		    end
		  | _ => raise SyntaxError
	      end
	end

    and parse_sequence_exp(tokens, fe) =	(* exp1 ; ... ; expn *)
	rr_parse(tokens, parse_exp fe, token_is_semicolon, build_seq_exp)

    and parse_listexp(tokens, fe) =
	build_listexp(comma_item_star_parse(tokens, parse_exp fe, token_is_rbrack))

    and parse_letexp(tokens, feIn) =
	let val (dec, feOut) = parse_dec(tokens, feIn, false)
	    val _ = parse_in tokens
	    val fe = fe_plus(feIn, feOut)
	    val exp = parse_sequence_exp(tokens, fe)
	    val _ = parse_end tokens
	in
	  Absyn.LETexp(dec, exp)
	end

    and parse_hashexp tokens =
	build_hashexp(parse_label tokens)

    and parse_appexp(tokens, fe) =
	let fun loop f =
	      case parse_atexp_opt(tokens, fe)
	       of SOME atexp => loop(Absyn.APPexp(f, atexp))
		| NONE => f
	in
	  loop(parse_atexp(tokens, fe))
	end

    and parse_infexp(tokens, fe) =
	parse_infix(tokens, fe, true, parse_appexp, build_infix_exp, NONE)

    and parse_exp fe tokens =
	let fun parse_exp_prio(tokens, fe, prioL) =
	      let fun loop expL =
		    let val tok = tokens_get tokens
			fun done() = (tokens_unget(tokens, tok); expL)
		    in
		      case tok
		       of Token.COLON =>	(* prio 9, always > prioL *)
			  loop(Absyn.TYPEDexp(expL, parse_ty tokens))
			| Token.ANDALSO =>	(* prio 8 *)
			  if prioL >= 8 then done()
			  else loop(build_andalso(expL, parse_exp_prio(tokens, fe, 8)))
			| Token.ORELSE =>	(* prio 7 *)
			  if prioL >= 7 then done()
			  else loop(build_orelse(expL, parse_exp_prio(tokens, fe, 7)))
			| Token.HANDLE =>	(* prio 6 *)
			  if prioL >= 6 then done()
			  else loop(Absyn.HANDLEexp(expL, parse_match(tokens, fe)))
			| tok => done()
		    end
	      in
		(* The relative priorities of the following cases don't matter,
		   only that they are all less than those of the operators above.  *)
		case tokens_get tokens
		 of Token.RAISE =>		(* prio 5 *)
		    loop(Absyn.RAISEexp(parse_exp_prio(tokens, fe, 5)))
		  | Token.IF =>			(* prio 4 *)
		    let val exp1 = parse_exp fe tokens
			val _ = parse_then tokens
			val exp2 = parse_exp fe tokens
			val _ = parse_else tokens
			val exp3 = parse_exp_prio(tokens, fe, 4)
		    in
		      loop(build_if_exp(exp1, exp2, exp3))
		    end
		  | Token.WHILE =>		(* prio 3 *)
		    let val exp1 = parse_exp fe tokens
			val _ = parse_do tokens
			val exp2 = parse_exp_prio(tokens, fe, 3)
		    in
		      loop(build_while_exp(exp1, exp2))
		    end
		  | Token.CASE =>		(* prio 2 *)
		    let val exp = parse_exp fe tokens
			val _ = parse_of tokens
			val match = parse_match(tokens, fe)
		    in
		      loop(build_case_exp(exp, match))
		    end
		  | Token.FN =>			(* prio 1 *)
		    loop(Absyn.FNexp(parse_match(tokens, fe)))
		  | tok => (tokens_unget(tokens, tok); loop(parse_infexp(tokens, fe)))
	      end
	in
	  parse_exp_prio(tokens, fe, 0)
	end

    and parse_match(tokens, fe) =
	Absyn.MATCH(bar_item_plus_parse(tokens, parse_mrule fe))

    and parse_mrule fe tokens =
	let val pat = parse_pat(tokens, fe)
	    val _ = parse_fatarrow tokens
	    val exp = parse_exp fe tokens
	in
	  (pat, exp)
	end

    (*
     * Grammar: Specifications and Signature Expressions
     *
     * spec	::= 'val' valdesc
     *		  | 'type' typdesc
     *		  | 'type' typdesc'						(derived form)
     *		  | 'eqtype' typdesc
     *		  | 'datatype' datdesc
     *		  | 'datatype' tycon '=' 'datatype' longtycon
     *		  | 'exception' exdesc
     *		  | 'structure' strdesc
     *		  | 'include' sigexp
     *		  | 'include' sigid1 ... sigidn					(n >= 2, derived form)
     *		  |								(empty)
     *		  | spec1 <';'> spec2						(Note 1)
     *		  | spec 'sharing' 'type' longtycon1 '=' ... '=' longtyconn	(n >= 2)
     *		  | spec 'sharing' longstrid1 '=' ... '=' longstridn		(n >= 2, derived form)
     * valdesc	::= vid ':' ty <'and' valdesc>
     * typdesc	::= tyvarseq tycon <'and' typdesc>
     * typdesc' ::= tyvarseq tycon '=' ty <'and' typdesc'>			(derived form)
     * datdesc	::= tyvarseq tycon '=' condesc <'and' datdesc>
     * condesc	::= vid <'of' ty> <'|' condesc>
     * exdesc	::= vid <'of' ty> <'and' condesc>
     * strdesc	::= strid ':' sigexp <'and' strdesc>
     *
     * sigexp	::= 'sig' spec 'end'
     *		  | sigid
     *		  | sigexp 'where' 'type' tyvarseq tycon '=' ty
     *		  | sigexp 'where' typdesc''					(derived form, Note 2)
     * typdesc''::= 'type' tyvarseq tycon '=' ty <'and' typdesc''>		(derived form, Note 2)
     *
     * sigdec	::= 'signature' sigbind
     * sigbind	::= sigid '=' sigexp <'and' sigbind>
     *
     * Note 1: Restriction: In a sequential specification, spec2 may not contain a sharing specification.
     * (From SuccessorML, "Fixing various minor issues with the formal syntax".)
     *
     * Note 2: A sigexp can be followed by "'and' strdesc" or "'and' sigbind", but can also
     * have "'and' 'type' tyvarseq tycon '=' ty" at its end, necessitating two tokens of
     * lookahead.  SuccessorML removes the "'and' 'type' ..." derived form from sigexps.
     *)

    fun parse_valdesc_item tokens =
      let val vid = parse_vid tokens
	  val _ = parse_colon tokens
	  val ty = parse_ty tokens
      in
	(vid, ty)
      end

    fun parse_val_spec tokens =
      Absyn.VALspec(and_item_plus_parse(tokens, parse_valdesc_item))

    fun parse_typdesc tokens = and_item_plus_parse(tokens, parse_tyvarseq_tycon)

    fun parse_type_spec tokens =
      let val (tyvarseq, tycon) = parse_tyvarseq_tycon tokens
      in
	case tokens_get tokens
	 of Token.AND =>
	    [Absyn.TYPEspec((tyvarseq, tycon) :: parse_typdesc tokens)]
	  | Token.EQ =>
	    let fun assemble(tyvarseq, tycon, ty) =
		  Absyn.INCLUDEspec(Absyn.WHEREsigexp(Absyn.SPECsigexp(Absyn.SPEC[Absyn.TYPEspec[(tyvarseq, tycon)]]),
						      tyvarseq, Absyn.LONGID([], tycon), ty))
		fun parse_item tokens =
		  let val (tyvarseq, tycon, ty) = parse_tyvarseq_tycon_eq_ty tokens
		  in
		    assemble(tyvarseq, tycon, ty)
		  end
		val ty = parse_ty tokens
		val first = assemble(tyvarseq, tycon, ty)
	    in
	      case tokens_get tokens
	       of Token.AND => List.rev(first :: and_item_plus_parse(tokens, parse_item))
		| tok => (tokens_unget(tokens, tok); [first])
	    end
	  | tok => (tokens_unget(tokens, tok); [Absyn.TYPEspec[(tyvarseq, tycon)]])
      end

    fun parse_eqtype_spec tokens = Absyn.EQTYPEspec(parse_typdesc tokens)

    fun parse_condesc_item tokens =
      let val vid = parse_vid tokens
	  val tyOpt = parse_ofty_opt tokens
      in
	(vid, tyOpt)
      end

    fun parse_condesc tokens =
      Absyn.CONBIND(bar_item_plus_parse(tokens, parse_condesc_item))

    fun parse_datdesc_item tokens =
      let val (tyvarseq, tycon) = parse_tyvarseq_tycon_eq tokens
	  val condesc = parse_condesc tokens
      in
	(tyvarseq, tycon, condesc)
      end

    fun parse_datdesc(datbOpt, tokens) =
      let fun parse() = and_item_plus_parse(tokens, parse_datdesc_item)
	  val datbinds =
	      case datbOpt
	       of NONE => parse()
		| SOME datb =>
		  case tokens_get tokens
		   of Token.AND => datb :: parse()
		    | tok => (tokens_unget(tokens, tok); [datb])
      in
	Absyn.DATBIND datbinds
      end

    fun parse_datatype_spec tokens =
      let fun do_datdesc datbOpt = Absyn.DATATYPEspec(parse_datdesc(datbOpt, tokens))
      in
	case tokens_get tokens
	 of Token.ID tycon =>
	    let val _ = parse_eq tokens
	    in
	      case tokens_get tokens
	       of Token.DATATYPE => Absyn.DATAREPLspec(tycon, parse_longtycon tokens)
		| tok =>
		  (* We've seen "datatype tycon = X" where X isn't "datatype",
		   * so we must have a condesc and possibly more datdescs.
		   * If our token pushback buffer was larger we could just
		   * push back "X", "=", and "tycon" and retry at datdesc.
		   * Instead we parse the first datdesc, and make parse_datdesc
		   * accept an optional pre-parsed datdesc.
		   *
		   * XXX: rewrite to use new unbounded buffer
		   *)
		  let val _ = tokens_unget(tokens, tok)
		      val condesc = parse_condesc tokens
		      val datb = ([], tycon, condesc)
		  in
		    do_datdesc(SOME datb)
		  end
	    end
	  | tok => (tokens_unget(tokens, tok); do_datdesc NONE)
      end

    val parse_exdesc_item = parse_condesc_item

    fun parse_exception_spec tokens =
      Absyn.EXspec(Absyn.CONBIND(and_item_plus_parse(tokens, parse_exdesc_item)))

    fun parse_longtycons tokens =
      let fun loop acc =
	    let val acc = parse_longtycon tokens :: acc
	    in
	      case tokens_get tokens
	       of Token.EQ => loop acc
		| tok => (tokens_unget(tokens, tok); List.rev acc)
	    end
	  val longtycon = parse_longtycon tokens
	  val _ = parse_eq tokens
      in
	loop [longtycon]
      end

    fun parse_sharing_longstrids tokens =
      let fun loop acc =
	    let val acc = parse_longstrid tokens :: acc
	    in
	      case tokens_get tokens
	       of Token.EQ => loop acc
		| tok => (tokens_unget(tokens, tok); List.rev acc)
	    end
	  val longstrid = parse_longstrid tokens
	  val _ = parse_eq tokens
      in
	loop [longstrid]
      end

    fun parse_sharing_spec(tokens, acc) =
      let fun parse spec =
	    case tokens_get tokens
	     of Token.TYPE => Absyn.SHARINGTYspec(spec, parse_longtycons tokens)
	      | tok =>
		let val _ = tokens_unget(tokens, tok)
		in
		  Absyn.SHARINGSTRspec(spec, parse_sharing_longstrids tokens)
		end
	  fun loop spec =
	    let val spec = parse spec
	    in
	      case tokens_get tokens
	       of Token.SHARING => loop(Absyn.SPEC[spec])
		| tok => (tokens_unget(tokens, tok); [spec])
	    end
      in
	loop(Absyn.SPEC(List.rev acc))
      end

    (* XXX: use new unbounded pushback buffer, do NOT return tok *)

    fun parse_sigexp_where(sigexp, tokens) =
      let fun loop sigexp =
	    let val _ = parse_type tokens
		val tyvarseq = parse_tyvarseq tokens
		val longtycon = parse_longtycon tokens
		val _ = parse_eq tokens
		val ty = parse_ty tokens
		val sigexp = Absyn.WHEREsigexp(sigexp, tyvarseq, longtycon, ty)
	    in
	      case tokens_get tokens
	       of Token.AND => loop sigexp
		| Token.WHERE => loop sigexp
		| tok => (tokens_unget(tokens, tok); (sigexp, tok))
	    end
      in
	loop sigexp
      end

    fun parse_sigexp_where_opt(sigexp, tokens) =
      case tokens_get tokens
       of Token.WHERE => parse_sigexp_where(sigexp, tokens)
	| tok => (sigexp, tok)

    fun parse_strid tokens =
      let val strid = parse_id tokens
	  val _ = check_strid strid
      in
	strid
      end

    val parse_sigid = parse_strid
    val parse_funid = parse_strid

    fun parse_spec tokens =
      let fun next acc = loop(acc, tokens_get tokens)
	  and loop(acc, tok) =
	      let fun onespec spec = next(spec :: acc)
		  fun specs s = next(s @ acc)
		  fun specntok(spec, tok) = loop(spec :: acc, tok)
		  fun specsntok(specs, tok) = loop(specs @ acc, tok)
	      in
		case tok
		 of Token.VAL => onespec(parse_val_spec tokens)
		  | Token.TYPE => specs(parse_type_spec tokens)
		  | Token.EQTYPE => onespec(parse_eqtype_spec tokens)
		  | Token.DATATYPE => onespec(parse_datatype_spec tokens)
		  | Token.EXCEPTION => onespec(parse_exception_spec tokens)
		  | Token.STRUCTURE => specntok(parse_structure_spec tokens)
		  | Token.INCLUDE => specsntok(parse_include_spec tokens)
		  | Token.SEMICOLON => next acc
		  | Token.SHARING => next(parse_sharing_spec(tokens, acc))
		  | _ => (Absyn.SPEC(List.rev acc), tok)
	      end
      in
	next []
      end

    and parse_structure_spec tokens =
	let fun loop acc =
	      let val strid = parse_strid tokens
		  val _ = parse_colon tokens
		  val (sigexp, tok) = parse_sigexp tokens
		  val acc = (strid, sigexp) :: acc
	      in
		case tok
		 of Token.AND => loop acc
		  | _ => (Absyn.STRUCTUREspec(List.rev acc), tok)
	      end
	in
	  loop []
	end

    and parse_include_spec tokens =
	case tokens_get tokens
	 of Token.ID id =>
	    let fun id2incl id = Absyn.INCLUDEspec(Absyn.SIGIDsigexp id)
		val _ = check_strid id
		val tok = tokens_get tokens
	    in
	      case tok
	       of Token.ID id2 =>
		  if is_strid id2 then
		    let fun loop specs =
			  let val tok = tokens_get tokens
			  in
			    case tok
			     of Token.ID id3 =>
				if is_strid id3 then loop(id2incl id3 :: specs)
				else (specs, tok)
			      | _ => (specs, tok)
			  end
		    in
		      loop [id2incl id2, id2incl id]
		    end
		  else ([id2incl id], tok)
		| Token.WHERE =>
		  let val (sigexp, tok) = parse_sigexp_where(Absyn.SIGIDsigexp id, tokens)
		  in
		    ([Absyn.INCLUDEspec sigexp], tok)
		  end
		| _ => ([id2incl id], tok)
	    end
	  | tok =>
	    let val _ = tokens_unget(tokens, tok)
		val (sigexp, tok) = parse_sigexp tokens
	    in
	      ([Absyn.INCLUDEspec sigexp], tok)
	    end

    and parse_sigexp tokens =
	case tokens_get tokens
	 of Token.SIG =>
	    let val (spec, tok) = parse_spec tokens
		val _ = check_end tok
	    in
	      parse_sigexp_where_opt(Absyn.SPECsigexp spec, tokens)
	    end
	  | Token.ID id =>
	    (check_strid id;
	     parse_sigexp_where_opt(Absyn.SIGIDsigexp id, tokens))
	  | tok => expected("sigexp", tok)

    fun parse_sigbind tokens =
      let fun loop acc =
	    let val sigid = parse_sigid tokens
		val _ = parse_eq tokens
		val (sigexp, tok) = parse_sigexp tokens
		val acc = (sigid, sigexp) :: acc
	    in
	      case tok
	       of Token.AND => loop acc
		| _ => (Absyn.SIGBIND(List.rev acc), tok)
	    end
      in
	loop []
      end

    (*
     * Grammar: Structure Expressions and Declarations
     *
     * strexp	::= 'struct' strdec 'end'
     *		  | longstrid
     *		  | strexp ':' sigexp
     *		  | strexp ':>' sigexp
     *		  | funid '(' strexp ')'
     *		  | funid '(' strdec ')'					(derived form)
     *		  | 'let' strdec 'in' strexp 'end'
     * strdec	::= dec								(Note 1)
     *		  | 'structure' strbind
     *		  | 'local' strdec1 'in' strdec2 'end'
     *		  |								(empty)
     *		  | strdec1 <';'> strdec2
     * strbind	::= strid '=' strexp <'and' strbind>
     *		  | strid ':' sigexp '=' strexp <'and' strbind>			(derived form)
     *		  | strid ':>' sigexp '=' strexp <'and' strbind>		(derived form)
     *
     * Note 1: Restriction: A declaration dec appearing in a structure declaration may not be
     * a sequential or local declaration.  (From SuccessorML, "Fixing various minor issues with
     * the formal syntax".)
     *)

    fun token_starts_dec tok =
      case tok	(* LOCAL and SEMICOLON deliberately excluded *)
       of Token.VAL => true
	| Token.FUN => true
	| Token.TYPE => true
	| Token.DATATYPE => true
	| Token.ABSTYPE => true
	| Token.EXCEPTION => true
	| Token.OPEN => true
	| Token.INFIX => true
	| Token.INFIXR => true
	| Token.NONFIX => true
	| _ => false

    fun token_starts_strdec tok =
      case tok	(* SEMICOLON deliberately excluded *)
       of Token.STRUCTURE => true
	| Token.LOCAL => true
	| _ => token_starts_dec tok

    fun token_starts_strexp tok =
      case tok
       of Token.STRUCT => true
	| Token.QUALID(_, id) => is_strid id
	| Token.ID id => is_strid id
	| Token.LET => true
	| _ => false

    fun apply_strexp_constraint_opt(NONE, strexp) = strexp
      | apply_strexp_constraint_opt(SOME f, strexp) = f strexp

    fun parse_strexp_constraint_opt_tok(tokens, tok) =
      case tok
       of Token.COLON =>
	  let val (sigexp, tok) = parse_sigexp tokens
	  in
	    (SOME(fn strexp => Absyn.TRANSPARENTstrexp(strexp, sigexp, ref NONE)), tok)
	  end
	| Token.COLONGT =>
	  let val (sigexp, tok) = parse_sigexp tokens
	  in
	    (SOME(fn strexp => Absyn.OPAQUEstrexp(strexp, sigexp, ref NONE)), tok)
	  end
	| tok => (NONE, tok)

    fun parse_strexp_constraint_opt tokens = parse_strexp_constraint_opt_tok(tokens, tokens_get tokens)

    fun parse_and_apply_strexp_constraint_opt(strexp, tokens) =
      let fun loop(strexp, tok) =
	    case parse_strexp_constraint_opt_tok(tokens, tok)
	     of (SOME f, tok) => loop(f strexp, tok)
	      | (NONE, tok) => (strexp, tok)
      in
	loop(strexp, tokens_get tokens)
      end

    fun parse_strdec(tokens, feIn, isTopDec) =
      let fun next(acc, feIn, feOut) = loop(acc, feIn, feOut, tokens_get tokens)
          and loop(acc, feIn, feOut, tok) =
	      let fun done() = (Absyn.STRDEC(List.rev acc), feOut)
		  fun decnfe(sdec, feOut') = next(sdec :: acc, fe_plus(feIn, feOut'), fe_plus(feOut, feOut'))
		  fun decntok(sdec, tok) = loop(sdec :: acc, feIn, feOut, tok)
	    in
	      case tok
	       of Token.STRUCTURE => decntok(parse_structure_strdec(tokens, feIn))
		| Token.LOCAL => decnfe(parse_local_strdec(tokens, feIn))
		| Token.SEMICOLON => if isTopDec then done() else next(acc, feIn, feOut)
		| tok =>
		  if token_starts_dec tok then decnfe(parse_dec_strdec(tokens, feIn, tok))
		  else (tokens_unget(tokens, tok); done())
	    end
      in
	next([], feIn, fe_empty)
      end

    and parse_structure_strdec(tokens, fe) =
	let fun loop acc =
	      let val strid = parse_strid tokens
		  val (constraintOpt, tok) = parse_strexp_constraint_opt tokens
		  val _ = check_eq tok
		  val (strexp, tok) = parse_strexp(tokens, fe)
		  val strexp = apply_strexp_constraint_opt(constraintOpt, strexp)
		  val acc = (strid, strexp) :: acc
	      in
		case tok
		 of Token.AND => loop acc
		  | _ => (Absyn.STRUCTUREstrdec(Absyn.STRBIND(List.rev acc)), tok)
	      end
	in
	  loop []
	end

    and parse_local_strdec(tokens, feIn) =
	let val (sdec1, feOut1) = parse_strdec(tokens, feIn, false)
	    val _ = parse_in tokens
	    val (sdec2, feOut2) = parse_strdec(tokens, fe_plus(feIn, feOut1), false)
	    val _ = parse_end tokens
	in
	  (Absyn.LOCALstrdec(sdec1, sdec2), feOut2)
	end

    and parse_dec_strdec(tokens, feIn, tok) =
	let val _ = tokens_unget(tokens, tok)
	    val (dec, feOut) = parse_dec(tokens, feIn, (*stopAtSemi=*)true)
	in
	  (Absyn.DECstrdec dec, feOut)
	end

    and parse_strexp(tokens, fe) =
	let val strexp =
		case tokens_get tokens
		 of Token.STRUCT => parse_struct_strexp(tokens, fe)
		  | Token.QUALID(strids, id) =>
		    (check_strid id; Absyn.LONGSTRIDstrexp(Absyn.LONGID(strids, id)))
		  | Token.ID id => parse_strid_strexp(tokens, fe, id)
		  | Token.LET => parse_let_strexp(tokens, fe)
		  | _ => raise SyntaxError
	in
	  parse_and_apply_strexp_constraint_opt(strexp, tokens)
	end

    and parse_struct_strexp(tokens, fe) =
	let val (strdec, _) = parse_strdec(tokens, fe, false)
	    val _ = parse_end tokens
	in
	  Absyn.STRUCTstrexp strdec
	end

    and parse_strid_strexp(tokens, fe, id) =
	let val _ = check_strid id
	in
	  case tokens_get tokens
	   of Token.LPAREN =>
	      let fun parse_strexp_or_strdec() =
		    let val tok = tokens_get tokens
		    in
		      if token_starts_strexp tok then
			(tokens_unget(tokens, tok);
			 parse_strexp(tokens, fe))
		      else if token_starts_strdec tok then
			let val _ = tokens_unget(tokens, tok)
			    val (strdec, _) = parse_strdec(tokens, fe, false)
			in
			  (Absyn.STRUCTstrexp strdec, tokens_get tokens)
			end
		      else raise SyntaxError
		    end
		  val (strexp, tok) = parse_strexp_or_strdec()
		  val _ = check_rparen tok
	      in
		Absyn.FUNAPPstrexp(id, strexp)
	      end
	    | tok => (tokens_unget(tokens, tok); Absyn.LONGSTRIDstrexp(Absyn.LONGID([], id)))
	end

    and parse_let_strexp(tokens, fe) =
	let val (strdec, feOut) = parse_strdec(tokens, fe, false)
	    val _ = parse_in tokens
	    val (strexp, tok) = parse_strexp(tokens, fe_plus(fe, feOut))
	    val _ = check_end tok
	in
	  Absyn.LETstrexp(strdec, strexp)
	end

    (*
     * Grammar: Functor Declarations, Top-level Declarations, and Programs
     *
     * fundec	::= 'functor' funbind
     * funbind	::= fundef <'and' funbind>
     * fundef	::= funid '(' strid ':' sigexp ')' '=' strexp
     *		  | funid '(' strid ':' sigexp ')' ':' sigexp' '=' strexp		(derived form)
     *		  | funid '(' strid ':' sigexp ')' ':>' sigexp' '=' strexp		(derived form)
     *		  | funid '(' spec ')' <':' sigexp> '=' strexp				(derived form)
     *		  | funid '(' spec ')' <':>' sigexp> '=' strexp				(derived form)
     *
     * topdec	::= strdec <topdec>							(Note 1)
     *		  | sigdec <topdec>
     *		  | fundec <topdec>
     *
     * program	::= topdec ';' <program>
     *		  | exp ';' <program>							(derived form)
     *
     * Note 1: Restriction: No topdec may contain, as an initial segment,
     * a strdec followed by a semicolon.
     * Furthermore, the strdec may not be a sequential declaration strdec1<;>strdec2.
     * (From SuccessorML, "Fixing various minor issues with the formal syntax".)
     *)

    fun parse_fundef_formal_arg tokens =
      case tokens_get tokens
       of Token.ID strid =>
	  let val _ = check_strid strid
	      val _ = parse_colon tokens
	      val (sigexp, tok) = parse_sigexp tokens
	  in
	    (strid, sigexp, fn strexp => strexp, tok)
	  end
	| tok =>
	  let val _ = tokens_unget(tokens, tok)
	      val (spec, tok) = parse_spec tokens
	      val strid = Absyn.gensym()
	      val sigexp = Absyn.SPECsigexp spec
	      fun wrap strexp =
		Absyn.LETstrexp(Absyn.STRDEC[Absyn.DECstrdec(Absyn.DEC[Absyn.OPENdec[Absyn.LONGID([], strid)]])],
				strexp)
	  in
	    (strid, sigexp, wrap, tok)
	  end

    fun parse_fundef(tokens, fe) =
      let val funid = parse_funid tokens
	  val _ = parse_lparen tokens
	  val (strid, sigexp, wrapStrExp, tok) = parse_fundef_formal_arg tokens
	  val _ = check_rparen tok
	  val (constraintOpt, tok) = parse_strexp_constraint_opt tokens
	  val _ = check_eq tok
	  val (strexp, tok) = parse_strexp(tokens, fe)
      in
	((funid, strid, sigexp, wrapStrExp(apply_strexp_constraint_opt(constraintOpt, strexp))), tok)
      end

    fun parse_funbind(tokens, fe) =
      let fun loop acc =
	    let val (fundef, tok) = parse_fundef(tokens, fe)
		val acc = fundef :: acc
	    in
	      case tok
	       of Token.AND => loop acc
		| _ => (Absyn.FUNBIND(List.rev acc), tok)
	    end
      in
	loop []
      end

    fun parse_topdec(tokens, fe) =
      case tokens_get tokens
       of Token.FUNCTOR =>
	  let val (funbind, tok) = parse_funbind(tokens, fe)
	      val _ = tokens_unget(tokens, tok)
	  in
	    SOME(Absyn.FUNDECtopdec funbind, fe)
	  end
	| Token.SIGNATURE =>
	  let val (sigbind, tok) = parse_sigbind tokens
	      val _ = tokens_unget(tokens, tok)
	  in
	    SOME(Absyn.SIGDECtopdec sigbind, fe)
	  end
	| Token.SEMICOLON => SOME(Absyn.STRDECtopdec(Absyn.STRDEC[]), fe)
	| Token.EOF => NONE
	| tok =>
	  let val _ = tokens_unget(tokens, tok)
	  in
	    if token_starts_strdec tok then
	      let val (strdec, feOut) = parse_strdec(tokens, fe, true)
	      in
		SOME(Absyn.STRDECtopdec strdec, fe_plus(fe, feOut))
	      end
	    else
	      let val exp = parse_exp fe tokens
		  val _ = (case tokens_get tokens
			    of Token.SEMICOLON => ()
			     | Token.EOF => ()
			     | _ => raise SyntaxError)
		  val dec = Absyn.DEC[Absyn.VALdec([], [(Absyn.VIDpat(Absyn.LONGID([], "it"), ref NONE), exp)], [])]
		  val strdec = Absyn.STRDEC[Absyn.DECstrdec dec]
	      in
		SOME(Absyn.STRDECtopdec strdec, fe)
	      end
	  end

    fun parse_file file =
      let val is = TextIO.openIn file
	  val lexarg = LexArg.new(file, is)
	  val tokens = tokens_open lexarg
      in
	case Util.after(fn() => parse_topdec(tokens, fe_init), fn() => TextIO.closeIn is)
	 of SOME(ast, _) => ast
	  | NONE => expected("topdec", Token.EOF)
      end

  end
