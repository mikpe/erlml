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
structure Lexer : LEXER =
  struct

    fun error(msg, pos1, pos2, lexarg) =
      (LexArg.error lexarg (msg, pos1, pos2);
       (Token.T(pos1, pos2, Token.ERROR), NONE))

    fun premature_eof(context, pos1, pos2, lexarg) =
      error("premature EOF in "^context, pos1, pos2, lexarg)

    fun unexpected(context, expected, got, pos1, pos2, lexarg) =
      error("in " ^ context ^ ", expected " ^ expected ^ ", got: " ^ Char.toString got, pos1, pos2, lexarg)

    (* ctype clone, for scanning sequences of characters of the same type
     * in identifiers and numerals;
     * encoding:
     * - bit 0( 1) is set for alphanumeric characters (A: 64+1)
     * - bit 1( 2) is set for hexadecimal digits (C: 64+2+1)
     * - bit 2( 4) is set for decimal digits (G: 64+4+2+1)
     * - bit 3( 8) is set for symbolic characters (H: 64+8)
     * - bit 6(64) is always set to make the codes readable (@)
     *)
    val ctype =
      (* 0-7     8-15    15-23   24-31    !"#$%&'()*+,-./0123456789:;<=>? *)
        "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@H@HHHHA@@HH@H@HGGGGGGGGGGH@HHHH\
        \HCCCCCCAAAAAAAAAAAAAAAAAAAA@H@HAHCCCCCCAAAAAAAAAAAAAAAAAAAA@H@H@"
      (* @ABCDEFGHIJKLMNOPQRSTUVWXYZ[\]^_`abcdefghijklmnopqrstyvwxyz{|}~DEL *)

    val ctype_alnum = Word.fromInt 1
    val ctype_hexdig = Word.fromInt 2
    val ctype_digit = Word.fromInt 4
    val ctype_symbol = Word.fromInt 8

    fun is_ctype(mask, ch) =
      if Char.ord ch < 128 then
	let val code = Word.fromInt(Char.ord(String.sub(ctype, Char.ord ch)))
	in
	  not(Word.andb(mask, code) = Word.fromInt 0)
	end
      else false

    fun scan_ctype(mask, acc, pos2, lexarg) =
      let fun loop(acc, pos2) =
	    case LexArg.input1 lexarg
	     of (NONE, _) => (acc, pos2, NONE)
	      | (SOME ch, pos3) =>
		if is_ctype(mask, ch) then loop(ch :: acc, pos3)
		else (acc, pos2, SOME(ch, pos3))
      in
	loop(acc, pos2)
      end

    fun mkintc acc =
      let val lexeme = List.rev acc
	  fun dointc() = Token.INTC(LexUtil.decint(String.implode lexeme))
	  fun donumc() = Token.NUMC(LexUtil.decint(String.implode lexeme))
      in
	case lexeme
	 of [#"0"] => Token.DIGZ
	  | [ch] => Token.DIGNZ(Char.ord ch - Char.ord #"0")
	  | #"~" :: _ => dointc()
	  | #"0" :: _ => dointc()
	  | _ => donumc()
      end

    fun mkwordc acc =
      Token.WORDC(LexUtil.decint(String.implode(List.rev acc)))

    fun mkhexc(isWord, acc) =
      let val i = LexUtil.hexint(String.implode(List.rev acc))
      in
	if isWord then Token.WORDC i else Token.INTC i
      end

    fun mkrealc acc =
      Token.REALC(LexUtil.rcon(String.implode(List.rev acc)))

    fun mkstringc acc =
      Token.STRINGC(String.implode(List.rev acc))

    (* seen "~"?<digit>+("."<digit>+)[eE], want "~"?<digit>+ *)
    fun scan_real_exponent(acc, pos1, pos2, lexarg) =
      let fun post_sign(ch, acc, pos2) =
	    if Char.isDigit ch then
	      let val (acc, pos2, lookahead) = scan_ctype(ctype_digit, ch :: acc, pos2, lexarg)
	      in
		(Token.T(pos1, pos2, mkrealc acc), lookahead)
	      end
            else unexpected("real exponent", "digit", ch, pos1, pos2, lexarg)
      in
	case LexArg.input1 lexarg
	 of (NONE, _) => premature_eof("real exponent", pos1, pos2, lexarg)
	  | (SOME ch, pos3) =>
	    if ch = #"~" then
	      case LexArg.input1 lexarg
	       of (NONE, _) => premature_eof("real exponent", pos1, pos2, lexarg)
		| (SOME ch, pos4) => post_sign(ch, #"~" :: acc, pos4)
	    else post_sign(ch, acc, pos3)
      end

    (* seen "~"?<digit>+".", want <digit>+<exponent>? *)
    fun scan_real_fraction(acc, pos1, pos2, lexarg) =
      case LexArg.input1 lexarg
       of (NONE, _) => premature_eof("real fraction", pos1, pos2, lexarg)
	| (SOME ch, pos3) =>
	  if Char.isDigit ch then
	    let val (acc, pos3, lookahead) = scan_ctype(ctype_digit, ch :: acc, pos3, lexarg)
	    in
	      case lookahead
	       of NONE => (Token.T(pos1, pos3, mkrealc acc), NONE)
		| SOME(ch, pos4) =>
		  if ch = #"e" orelse ch = #"E" then scan_real_exponent(ch :: acc, pos1, pos4, lexarg)
		  else (Token.T(pos1, pos3, mkrealc acc), SOME(ch, pos4))
	    end
	  else unexpected("real fraction", "digit", ch, pos1, pos3, lexarg)

    fun scan_decimal_integer_post_ch(ch, acc, pos1, pos2, pos3, lexarg) =
      if ch = #"." then scan_real_fraction(ch :: acc, pos1, pos3, lexarg)
      else if ch = #"e" orelse ch = #"E" then scan_real_exponent(ch :: acc, pos1, pos3, lexarg)
      else (Token.T(pos1, pos2, mkintc acc), SOME(ch, pos3))

    fun scan_decimal_integer(acc, pos1, pos2, lexarg) =
      let val (acc, pos2, lookahead) = scan_ctype(ctype_digit, acc, pos2, lexarg)
      in
	case lookahead
	 of NONE => (Token.T(pos1, pos2, mkintc acc), NONE)
	  | SOME(ch, pos3) => scan_decimal_integer_post_ch(ch, acc, pos1, pos2, pos3, lexarg)
      end

    (* seen (~?0|0w)x, want <hexdigit>+ *)
    fun scan_hex(acc, pos1, pos2, isWord, lexarg) =
      case LexArg.input1 lexarg
       of (NONE, _) => premature_eof("hex constant", pos1, pos2, lexarg)
	| (SOME ch, pos2) =>
	  if Char.isHexDigit ch then
	    let val (acc, pos2, lookahead) = scan_ctype(ctype_hexdig, ch :: acc, pos2, lexarg)
	    in
	      (Token.T(pos1, pos2, mkhexc(isWord, acc)), lookahead)
	    end
	  else unexpected("hex constant", "hex digit", ch, pos1, pos2, lexarg)

    (* seen ~?0x, want <hexdigit>+ *)
    fun scan_hex_integer(acc, pos1, pos2, lexarg) = scan_hex(acc, pos1, pos2, false, lexarg)

    (* seen 0wx, want <hexdigit>+ *)
    fun scan_hex_word(acc, pos1, pos2, lexarg) = scan_hex(acc, pos1, pos2, true, lexarg)

    (* seen 0w, want <digit>+ *)
    fun scan_decimal_word(ch, acc, pos1, pos2, lexarg) =
      if Char.isDigit ch then
	let val (acc, pos2, lookahead) = scan_ctype(ctype_digit, ch :: acc, pos2, lexarg)
	in
	  (Token.T(pos1, pos2, mkwordc acc), lookahead)
	end
      else unexpected("word constant", "digit", ch, pos1, pos2, lexarg)

    (* PRE: seen "~"?<digit> *)
    fun scan_number(ch, acc, pos1, pos2, lexarg) =
      if ch = #"0" then	(* check for "0x", "0wx", "0w" *)
	case LexArg.input1 lexarg
	 of (NONE, _) => (Token.T(pos1, pos2, mkintc(ch :: acc)), NONE)
	  | (SOME ch, pos3) =>
	    case ch
	     of #"x" => scan_hex_integer(#"x" :: #"0" :: acc, pos1, pos3, lexarg)
	      | #"w" =>	(* 0w<digit>+ or 0wx<hexdigit>+, must not have ~ prefix *)
		(case acc
		  of _ :: _ => error("invalid word constant", pos1, pos3, lexarg)
		   | [] =>	(* no ~ prefix, Ok *)
		     case LexArg.input1 lexarg
		      of (NONE, pos4) => premature_eof("word constant", pos1, pos4, lexarg)
		       | (SOME ch, pos4) =>
			 let val acc = [#"w", #"0"]
			 in
			   case ch
			    of #"x" => scan_hex_word(#"x" :: acc, pos1, pos4, lexarg)
			     | _ => scan_decimal_word(ch, acc, pos1, pos4, lexarg)
			 end)
	      | _ =>
		if Char.isDigit ch then scan_decimal_integer(ch :: #"0" :: acc, pos1, pos3, lexarg)
		else scan_decimal_integer_post_ch(ch, #"0" :: acc, pos1, pos2, pos3, lexarg)
      else scan_decimal_integer(ch :: acc, pos1, pos2, lexarg)

    fun scan_symbolic_id(acc, pos1, pos2, lexarg) =
      let val (acc, pos2, lookahead) = scan_ctype(ctype_symbol, acc, pos2, lexarg)
	  val buf = String.implode(List.rev acc)
	  val tok =
	      case buf
	       of ":" => Token.COLON
		| "=" => Token.EQ
		| "=>" => Token.FATARROW
		| "->" => Token.THINARROW
		| "#" => Token.HASH
		| "*" => Token.STAR
		| "|" => Token.BAR
		| ":>" => Token.COLONGT
		| _ => Token.ID buf
      in
	(Token.T(pos1, pos2, tok), lookahead)
      end

    fun scan_tilde(pos1, lexarg) =
      case LexArg.input1 lexarg
       of (NONE, _) => (Token.T(pos1, pos1, Token.ID "~"), NONE)
	| (SOME ch, pos2) =>
	  if is_ctype(ctype_digit, ch) then scan_number(ch, [#"~"], pos1, pos2, lexarg)
	  else if is_ctype(ctype_symbol, ch) then scan_symbolic_id([ch, #"~"], pos1, pos2, lexarg)
	  else (Token.T(pos1, pos1, Token.ID "~"), SOME(ch, pos2))

    fun scan_one_alpha(ch, pos1, lexarg) =
      let val (acc, pos2, lookahead) = scan_ctype(ctype_alnum, [ch], pos1, lexarg)
	  val buf = String.implode(List.rev acc)
	  val tok =
	      case buf
	       of "abstype" => Token.ABSTYPE
		| "and" => Token.AND
		| "andalso" => Token.ANDALSO
		| "as" => Token.AS
		| "case" => Token.CASE
		| "datatype" => Token.DATATYPE
		| "do" => Token.DO
		| "else" => Token.ELSE
		| "end" => Token.END
		| "exception" => Token.EXCEPTION
		| "fn" => Token.FN
		| "fun" => Token.FUN
		| "handle" => Token.HANDLE
		| "if" => Token.IF
		| "in" => Token.IN
		| "infix" => Token.INFIX
		| "infixr" => Token.INFIXR
		| "let" => Token.LET
		| "local" => Token.LOCAL
		| "nonfix" => Token.NONFIX
		| "of" => Token.OF
		| "op" => Token.OP
		| "orelse" => Token.ORELSE
		| "raise" => Token.RAISE
		| "rec" => Token.REC
		| "then" => Token.THEN
		| "type" => Token.TYPE
		| "val" => Token.VAL
		| "with" => Token.WITH
		| "withtype" => Token.WITHTYPE
		| "while" => Token.WHILE
		| "eqtype" => Token.EQTYPE
		| "functor" => Token.FUNCTOR
		| "include" => Token.INCLUDE
		| "sharing" => Token.SHARING
		| "sig" => Token.SIG
		| "signature" => Token.SIGNATURE
		| "struct" => Token.STRUCT
		| "structure" => Token.STRUCTURE
		| "where" => Token.WHERE
		| _ => Token.ID buf
      in
	(Token.T(pos1, pos2, tok), lookahead)
      end

    fun scan_qualid(strids, pos1, pos2, lexarg) =
      case LexArg.input1 lexarg
       of (NONE, _) => premature_eof("qualified identifier", pos1, pos2, lexarg)
	| (SOME ch, pos3) =>
	  if is_ctype(ctype_symbol, ch) then
	    case scan_symbolic_id([ch], pos3, pos3, lexarg)
	     of (Token.T(_, pos4, Token.ID s), lookahead) => (Token.T(pos1, pos4, Token.QUALID(List.rev strids, s)), lookahead)
	      | (Token.T(_, pos4, Token.STAR), lookahead) => (Token.T(pos1, pos4, Token.QUALID(List.rev strids, "*")), lookahead)
	      | (Token.T(_, pos4, _), lookahead) => error("invalid qualified identifier", pos1, pos4, lexarg)
	  else if Char.isAlpha ch then
	    case scan_one_alpha(ch, pos3, lexarg)
	     of (Token.T(_, _, Token.ID s), SOME(#".", pos4)) => scan_qualid(s :: strids, pos1, pos4, lexarg)
	      | (Token.T(_, pos4, Token.ID s), lookahead) => (Token.T(pos1, pos4, Token.QUALID(List.rev strids, s)), lookahead)
	      | (Token.T(_, pos4, _), lookahead) => error("invalid qualified identifier", pos1, pos4, lexarg)
	  else unexpected("qualified identifier", "letter or symbol", ch, pos1, pos3, lexarg)

    fun scan_alpha(ch, pos1, lexarg) =
      case scan_one_alpha(ch, pos1, lexarg)
       of (Token.T(_, _, Token.ID s), SOME(#".", pos3)) => scan_qualid([s], pos1, pos3, lexarg)
	| (tok, lookahead) => (tok, lookahead)

    fun scan_tyvar(pos1, lexarg) =
      let val (acc, pos2, lookahead) = scan_ctype(ctype_alnum, [], pos1, lexarg)
      in
	case acc
	 of [] => error("invalid type variable", pos1, pos2, lexarg)
	  | _ => (Token.T(pos1, pos2, Token.TYVAR(String.implode(List.rev acc))), lookahead)
      end

    fun scan_string(acc, pos1, lexarg) =
      case LexArg.input1 lexarg
       of (NONE, pos2) => premature_eof("string constant", pos1, pos2, lexarg)
	| (SOME ch, pos2) =>
	  case ch
	   of #"\"" => (Token.T(pos1, pos2, mkstringc acc), NONE)
	    | #"\\" =>
	      (case LexArg.input1 lexarg
		of (NONE, pos2) => premature_eof("string constant", pos1, pos2, lexarg)
		 | (SOME ch, pos2) =>
		   case ch
		    of #"a" => scan_string((Char.chr 7) :: acc, pos1, lexarg)
		     | #"b" => scan_string((Char.chr 8) :: acc, pos1, lexarg)
		     | #"t" => scan_string((Char.chr 9) :: acc, pos1, lexarg)
		     | #"n" => scan_string((Char.chr 10) :: acc, pos1, lexarg)
		     | #"v" => scan_string((Char.chr 11) :: acc, pos1, lexarg)
		     | #"f" => scan_string((Char.chr 12) :: acc, pos1, lexarg)
		     | #"r" => scan_string((Char.chr 13) :: acc, pos1, lexarg)
		     | #"\"" => scan_string(ch :: acc, pos1, lexarg)
		     | #"\\" => scan_string(ch :: acc, pos1, lexarg)
		     | #"^" =>	(* \^C for C in [@, _] *)
		       (case LexArg.input1 lexarg
			 of (NONE, pos2) => premature_eof("string constant", pos1, pos2, lexarg)
			  | (SOME ch, pos2) =>
			    if Char.ord ch >= 64 andalso Char.ord ch <= 95
			    then scan_string((Char.chr(Char.ord ch - 64)) :: acc, pos1, lexarg)
			    else unexpected("string escape", "character in [@,_]", ch, pos1, pos2, lexarg))
		     | #"u" => scan_hex4(acc, pos1, lexarg)
		     | _ =>
		       if Char.isDigit ch then scan_dig3(ch, acc, pos1, lexarg)
		       else if Char.isSpace ch then scan_gap(acc, pos1, lexarg)
		       else unexpected("string escape", "whitespace, digit, or [abtnvfru^\\\"]", ch, pos1, pos2, lexarg))
	    | _ =>
	      if Char.isPrint ch then scan_string(ch :: acc, pos1, lexarg)
	      else unexpected("string constant", "\", \\, or printable character", ch, pos1, pos2, lexarg)

    and scan_hex4(acc, pos1, lexarg) =	(* \uxxxx, seen \u *)
      let fun hexdig_value ch = (* XXX: similar code in LexUtil *)
	    if ch >= #"a" then Char.ord ch - (Char.ord #"a" - 10)
	    else if ch >= #"A" then Char.ord ch - (Char.ord #"A" - 10)
	    else Char.ord ch - Char.ord #"0"
	  fun loop(0, v) = scan_string((Char.chr v) :: acc, pos1, lexarg)
	    | loop(n, v) =
	      case LexArg.input1 lexarg
	       of (NONE, pos2) => premature_eof("string escape", pos1, pos2, lexarg)
		| (SOME ch, pos2) =>
		  if Char.isHexDigit ch then loop(n - 1, v * 16 + hexdig_value ch)
		  else unexpected("string escape", "hex digit", ch, pos1, pos2, lexarg)
      in
	loop(4, 0)
      end

    and scan_dig3(ch, acc, pos1, lexarg) =	(* \ddd, seen \d *)
      let fun digit_value ch = Char.ord ch - Char.ord #"0"
	  fun loop(0, v) = scan_string((Char.chr v) :: acc, pos1, lexarg)
	    | loop(n, v) =
	      case LexArg.input1 lexarg
	       of (NONE, pos2) => premature_eof("string escape", pos1, pos2, lexarg)
		| (SOME ch, pos2) =>
		  if Char.isDigit ch then loop(n - 1, v * 10 + digit_value ch)
		  else unexpected("string escape", "digit", ch, pos1, pos2, lexarg)
      in
	loop(2, digit_value ch)
      end

    and scan_gap(acc, pos1, lexarg) =	(* skip <space>*\\ *)
	let fun loop() =
	      case LexArg.input1 lexarg
	       of (NONE, pos2) => premature_eof("string gap", pos1, pos2, lexarg)
		| (SOME ch, pos2) =>
		  if ch = #"\\" then scan_string(acc, pos1, lexarg)
		  else if Char.isSpace ch then loop()
		  else unexpected("string gap", "whitespace or \\", ch, pos1, pos2, lexarg)
	in
	  loop()
	end

    fun scan_char_con(pos1, pos2, lexarg) =
      let val (Token.T(_, pos3, tok), lookahead) = scan_string([], pos2, lexarg)
      in
	case tok
	 of Token.STRINGC str =>
	    (case String.size str
	      of 1 => (Token.T(pos1, pos3, Token.CHARC(String.sub(str, 0))), lookahead)
	       | _ => error("invalid character constant", pos1, pos3, lexarg))
	  | _ => error("invalid character constant", pos1, pos3, lexarg)
      end

    fun scan_hash(pos1, lexarg) =
      case LexArg.input1 lexarg
       of (NONE, pos2) => (Token.T(pos1, pos1, Token.HASH), NONE)
	| (SOME ch, pos2) =>
	  if ch = #"\"" then scan_char_con(pos1, pos2, lexarg)
	  else if is_ctype(ctype_symbol, ch) then scan_symbolic_id([ch, #"#"], pos1, pos2, lexarg)
	  else (Token.T(pos1, pos1, Token.HASH), SOME(ch, pos2))

    fun scan_comment lexarg = (* returns NONE on success or SOME pos on premature EOF *)
      let fun outer level =
	    let fun inner() =
		  let fun lparen() =
			case LexArg.input1 lexarg
			 of (NONE, pos) => SOME pos
			  | (SOME ch, _) =>
			    case ch
			     of #"*" => outer(level + 1)
			      | #"(" => lparen()
			      | _ => inner()
		      fun star() =
			case LexArg.input1 lexarg
			 of (NONE, pos) => SOME pos
			  | (SOME ch, _) =>
			    case ch
			     of #")" =>
				let val level = level - 1
				in
				  if level = 0 then NONE else outer level
				end
			      | #"*" => star()
			      | #"(" => lparen()
			      | _ => inner()
		  in
		    case LexArg.input1 lexarg
		     of (NONE, pos) => SOME pos
		      | (SOME ch, _) =>
			case ch
			 of #"(" => lparen()
			  | #"*" => star()
			  | _ => inner()
		  end
	    in
	      inner()
	    end
      in
	outer 1
      end

    fun scan_dot(pos1, lexarg) =
      let fun loop(0, pos2) = (Token.T(pos1, pos2, Token.DOTDOTDOT), NONE)
	    | loop(n, _) =
	      case LexArg.input1 lexarg
	       of (SOME #".", pos2) => loop(n - 1, pos2)
		| (SOME ch, pos2) => unexpected("...", ".", ch, pos1, pos2, lexarg)
		| (NONE, pos2) => premature_eof("...", pos1, pos2, lexarg)
      in
	loop(2, pos1)
      end

    datatype chclass
      = SPACE
      | SYMBOL	(* sans TILDE and HASH *)
      | TILDE	(* special case of SYMBOL *)
      | HASH	(* special case of SYMBOL *)
      | DQUOTE
      | SQUOTE
      | LPAREN
      | RPAREN
      | COMMA
      | DOT
      | DIGIT
      | SEMICOLON
      | ALPHA
      | LBRACK
      | RBRACK
      | UNDERSCORE
      | LBRACE
      | RBRACE
      | ERROR

    fun chclass ch =
      case ch
       of #"!" => SYMBOL
	| #"\"" => DQUOTE
	| #"#" => HASH		(* should be SYMBOL, but we must check for character constant *)
	| #"$" => SYMBOL
	| #"%" => SYMBOL
	| #"&" => SYMBOL
	| #"'" => SQUOTE
	| #"(" => LPAREN
	| #")" => RPAREN
	| #"*" => SYMBOL
	| #"+" => SYMBOL
	| #"," => COMMA
	| #"-" => SYMBOL
	| #"." => DOT
	| #"/" => SYMBOL
	| #":" => SYMBOL
	| #";" => SEMICOLON
	| #"<" => SYMBOL
	| #"=" => SYMBOL
	| #">" => SYMBOL
	| #"?" => SYMBOL
	| #"@" => SYMBOL
	| #"[" => LBRACK
	| #"\\" => SYMBOL
	| #"]" => RBRACK
	| #"^" => SYMBOL
	| #"_" => UNDERSCORE
	| #"`" => SYMBOL
	| #"{" => LBRACE
	| #"|" => SYMBOL
	| #"}" => RBRACE
	| #"~" => TILDE		(* should be SYMBOL, but we must check for ~<numerical constant> *)
	| _ =>
	  if Char.isDigit ch then DIGIT
	  else if Char.isAlpha ch then ALPHA
	  else if Char.isSpace ch then SPACE
	  else ERROR

    fun scan_start lexarg =
      case LexArg.input1 lexarg
       of (NONE, pos) => (Token.T(pos, pos, Token.EOF), NONE)
	| (SOME ch, pos) =>
	  case chclass ch
	   of SYMBOL => scan_symbolic_id([ch], pos, pos, lexarg)
	    | DQUOTE => scan_string([], pos, lexarg)
	    | HASH => scan_hash(pos, lexarg)
	    | SQUOTE => scan_tyvar(pos, lexarg)
	    | LPAREN => scan_lparen(pos, lexarg)
	    | RPAREN => (Token.T(pos, pos, Token.RPAREN), NONE)
	    | COMMA => (Token.T(pos, pos, Token.COMMA), NONE)
	    | DOT => scan_dot(pos, lexarg)
	    | SEMICOLON => (Token.T(pos, pos, Token.SEMICOLON), NONE)
	    | LBRACK => (Token.T(pos, pos, Token.LBRACK), NONE)
	    | RBRACK => (Token.T(pos, pos, Token.RBRACK), NONE)
	    | UNDERSCORE => (Token.T(pos, pos, Token.UNDERSCORE), NONE)
	    | LBRACE => (Token.T(pos, pos, Token.LBRACE), NONE)
	    | RBRACE => (Token.T(pos, pos, Token.RBRACE), NONE)
	    | TILDE => scan_tilde(pos, lexarg)
	    | DIGIT => scan_number(ch, [], pos, pos, lexarg)
	    | ALPHA => scan_alpha(ch, pos, lexarg)
	    | SPACE => scan_start lexarg
	    | ERROR => error("invalid character", pos, pos, lexarg)

    and scan_lparen(pos1, lexarg) =
	case LexArg.input1 lexarg
	 of (NONE, _) => (Token.T(pos1, pos1, Token.LPAREN), NONE)
	  | (SOME ch, pos) =>
	    case ch
	     of #"*" =>
		(case scan_comment lexarg
		  of NONE => scan_start lexarg
		   | SOME pos2 => premature_eof("comment", pos1, pos2, lexarg))
	      | _ => (Token.T(pos1, pos1, Token.LPAREN), SOME(ch, pos))

    fun lex lexarg =
      let val (token, lookahead) = scan_start lexarg
      in
	case lookahead
	 of NONE => ()
	  | SOME(ch, pos) => LexArg.unget1(lexarg, ch, pos);
	token
      end

  end
