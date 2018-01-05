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
 *
 * Core Erlang representation.
 *
 * Omissions:
 * - literals omit binaries and maps
 * - 'case' clauses omit guards
 * - all entities omit annotations
 * - no support for multiple values, so 'let' binds a single variable, 'of' in
 *   'try' binds a single variable, and 'case' clauses have a single pattern
 * - 'apply' requires the function position to be a variable rather than any
 *   expression, for bug compatibility with OTP < 20.1 (see OTP PR #1526)
 *)
structure CoreErlang : CORE_ERLANG =
  struct

    type atom = string
    type integer = IntInf.int
    type float = real
    type var = string

    datatype literal
      = L_ATOM of atom
      | L_INTEGER of integer
      | L_FLOAT of float
      | L_STRING of string
      | L_NIL

    datatype constant
      = C_LITERAL of literal
      | C_CONS of constant * constant
      | C_TUPLE of constant list

    datatype pat
      = P_LITERAL of literal
      | P_CONS of pat * pat
      | P_TUPLE of pat list
      | P_VARIABLE of var
      | P_ALIAS of var * pat

    datatype fname
      = FNAME of atom * int

    datatype fvar
      = FV of var
      | FN of fname

    datatype expr
      = E_LITERAL of literal
      | E_CONS of expr * expr
      | E_TUPLE of expr list
      | E_VARIABLE of var
      | E_FNAME of fname
      | E_FUN of funexpr
      | E_LET of var * expr * expr
      | E_LETREC of (fname * funexpr) list * expr
      | E_APPLY of fvar * expr list
      | E_CALL of expr * expr * expr list
      | E_PRIMOP of atom * expr list
      | E_CASE of expr * (pat * expr) list
      | E_TRY of expr * var * expr * var * var * var * expr

    and funexpr
      = FUN of var list * expr

    datatype module
      = MODULE of atom * fname list * (atom * constant) list * (fname * funexpr) list

    val mkVar =
	let val counter = ref 0
	in
	  fn (SOME name) => "V" ^ name
           | NONE =>
	     let val c = 1 + !counter
	     in
	       counter := c;
	       "V" ^ Int.toString c
	     end
	end

    (* convert basic entities to Core Erlang notation *)

    fun tildeToDash #"~" = #"-"
      | tildeToDash c = c

    fun integerToString int =
      String.map tildeToDash (IntInf.toString int)

    (* TODO: work around Moscow ML lack of Real.isFinite
    exception BadFloat of real

    fun floatToString f =
      if Real.isFinite f then String.map tildeToDash (Real.toString f)
      else raise (BadFloat f)
    *)
    fun floatToString float =
      String.map tildeToDash (Real.toString float)

    fun charToOctal3 c =
      let val s = Int.fmt StringCvt.OCT (Char.ord c)
      in
	case String.size s
	 of 1 => "00" ^ s
	  | 2 => "0" ^ s
	  | _ => s
      end

    fun escapeString(s, quote) =
      let fun escape c =
	    case c
	     of
	      (* Escapes that are the same in SML and Core Erlang *)
	        #"\b"     => [#"\\", #"b"]
	      | #"\t"     => [#"\\", #"t"]
	      | #"\n"     => [#"\\", #"n"]
	      | #"\v"     => [#"\\", #"v"]
	      | #"\f"     => [#"\\", #"f"]
	      | #"\r"     => [#"\\", #"r"]
	      | #"\\"     => [#"\\", #"\\"]
	      (* Core Erlang only escapes (except for the single and double quotes) *)
	      | #"\u001b" => [#"\\", #"e"]
	      | #" "      => [#"\\", #"s"]
	      | #"\u007f" => [#"\\", #"d"]
	      (* \a for \u0007 is SML-only *)
	      | _ =>
		if c = quote then [#"\\", c]
		else if Char.isPrint c then [c]
		else #"\\" :: String.explode(charToOctal3 c)
	  fun loop([], res) = String.implode(quote :: List.rev(quote :: res))
	    | loop(c :: cs, res) = loop(cs, List.rev(escape c) @ res)
      in
	loop(String.explode s, [])
      end

    fun atomToString atom = escapeString(atom, #"'")

    fun stringToString str = escapeString(str, #"\"")

    fun varToString var =
      let fun mangle c = (* _OOO *)
	    #"_" :: String.explode(charToOctal3 c)
	  fun toInitial c =
	    if c = #"_" then [c, c]
	    else if Char.isUpper c then [c]
	    else mangle c
	  fun toSubsequent c =
	    case c
	     of #"_" => [c, c]
	      | #"@" => [c]
	      | _ =>
		if Char.isAlphaNum c then [c]
		else mangle c
	  fun loop([], res) = String.implode(List.rev res)
	    | loop(c :: cs, res) = loop(cs, List.rev(toSubsequent c) @ res)
	  val cs = String.explode var
      in
	loop(tl cs, List.rev(toInitial(hd cs)))
      end

  end
