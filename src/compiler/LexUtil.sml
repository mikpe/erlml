(*
 * Copyright 1997, 2015-2018 Mikael Pettersson
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
structure LexUtil : LEXUTIL =
  struct

    fun mkinfint(s, indx) =
      let val size = String.size s
	  val (isneg, indx) = case String.sub(s, indx)
			       of #"~"	=> (true, indx + 1)
				| _	=> (false, indx)
	  fun scan(i, indx) =
	    (* This does a "i * 10 - c" loop followed by a negation if the
	       number is positive, because that gives extra precision with
	       fixed-precision 'int'.  IntInf.int doesn't need that, but
	       this makes the code more reusable.  *)
	    if indx < size then
	      let val c = Char.ord(String.sub(s, indx)) - Char.ord #"0"
		  val i = IntInf.-(IntInf.*(i, IntInf.fromInt 10), IntInf.fromInt c)
	      in
		scan(i, indx + 1)
	      end
	    else if isneg then i else IntInf.~ i
      in
	scan(IntInf.fromInt 0, indx)
      end

    fun mkint(s, indx) = IntInf.toInt(mkinfint(s, indx))

    fun decint s = mkinfint(s, 0)

    fun hexint s =	(* (~?0|0w)x{hexdigit}+ *)
      let val size = String.size s
	  val indx = 0
	  val (isneg, indx) = case String.sub(s, indx)
			       of #"~"	=> (true, indx + 1)
				| _	=> (false, indx)
	  val indx = indx + 1	(* skip "0" *)
	  val indx = case String.sub(s, indx)
		      of #"w" => indx + 1
		       | _ => indx
	  val indx = indx + 1	(* skip "x" *)
	  fun digit c =
	    if c >= #"a" then Char.ord c - (Char.ord #"a" - 10)
	    else if c >= #"A" then Char.ord c - (Char.ord #"A" - 10)
	    else Char.ord c - Char.ord #"0"
	  fun scan(i, indx) =
	    if indx < size then
	      let val c = digit(String.sub(s, indx))
		  val i = IntInf.-(IntInf.*(i, IntInf.fromInt 16), IntInf.fromInt c)
	      in
		scan(i, indx + 1)
	      end
	    else if isneg then i else IntInf.~ i
      in
	scan(IntInf.fromInt 0, indx)
      end
(*
    fun icon s =
      let val size = String.size s
	  fun hex_dig indx =
	    if indx >= size then NONE
	    else
	      let val c = String.sub(s, indx)
	      in
		if (c >= #"0" andalso c <= #"9") orelse
		   (c >= #"A" andalso c <= #"F") orelse
		   (c >= #"a" andalso c <= #"f")
		  then SOME(hexint s)
		else NONE
	      end
	  fun hex_pfx indx =
	    if indx >= size then SOME(IntInf.fromInt 0)
	    else
	      let val c = String.sub(s, indx)
	      in
		if c = #"x" then hex_dig(indx + 1)
		else if c >= #"0" andalso c <= #"9" then SOME(decint s)
		else NONE
	      end
	  fun after_sign indx =
	    if indx >= size then NONE
	    else
	      let val c = String.sub(s, indx)
	      in
		if c = #"0" then hex_pfx(indx + 1)
		else if c >= #"1" andalso c <= #"9" then SOME(decint s)
		else NONE
	      end
	  fun sign indx =
	    if indx >= size then NONE
	    else
	      case String.sub(s, indx)
		of #"~"	=> after_sign(indx + 1)
		 | _	=> after_sign indx
      in
	sign 0
      end
*)
    fun mkreal(s, indx) =
      let val size = String.size s
	  val (isneg, indx) = case String.sub(s, indx)
			       of #"~"	=> (true, indx + 1)
				| _	=> (false, indx)
	  fun apply_sign f = if isneg then ~f else f
	  fun scale(f, _, 0) = apply_sign f
	    | scale(f, x, e) = scale(f * x, x, e - 1)
	  fun exp(f, e, indx) =
	    let val e = mkint(s, indx) - e
	    in
	      scale(f, if e < 0 then 0.10 else 10.0, abs e)
	    end
	  fun frac(f, e, indx) =
	    if indx < size then
	      let val c = String.sub(s, indx)
	      in
		if c >= #"0" andalso c <= #"9" then
		  frac(f * 10.0 + real(Char.ord c - Char.ord #"0"), e + 1, indx + 1)
		else if c = #"e" orelse c = #"E" then exp(f, e, indx + 1)
		else scale(f, 0.10, e)
	      end
	    else scale(f, 0.10, e)
	  fun start(f, indx) =
	    if indx < size then
	      let val c = String.sub(s, indx)
	      in
		if c >= #"0" andalso c <= #"9" then
		  start(f * 10.0 + real(Char.ord c - Char.ord #"0"), indx + 1)
		else if c = #"." then frac(f, 0, indx + 1)
		else if c = #"e" orelse c = #"E" then exp(f, 0, indx + 1)
		else apply_sign f
	      end
	    else apply_sign f
      in
	start(0.0, indx)
      end

    fun rcon s = mkreal(s, 0)
(*
    fun escseq(s, i) =
      let fun echar #"n" = #"\n"	(* Char.chr 10 *)
	    | echar #"r" = #"\r"	(* Char.chr 13 *)
	    | echar #"t" = #"\t"	(* Char.chr  9 *)
	    | echar #"f" = #"\f"	(* Char.chr 12 *)
	    | echar #"a" = #"\a"	(* Char.chr  7 *)
	    | echar #"b" = #"\b"	(* Char.chr  8 *)
	    | echar #"v" = #"\v"	(* Char.chr 11 *)
	    | echar c = c	(* #"\\" and #"\"" *)
	  fun cntrl c = Char.chr((Char.ord c - 64) mod 128)
	  val c = String.sub(s, i)
      in
	if c >= #"0" andalso c <= #"9" then
	  let val d1 = Char.ord c		      - Char.ord #"0"
	      and d2 = Char.ord(String.sub(s, i + 1)) - Char.ord #"0"
	      and d3 = Char.ord(String.sub(s, i + 2)) - Char.ord #"0"
	  in
	    (Char.chr(d1 * 100 + d2 * 10 + d3), i + 3)
	  end
	else if c = #"^" then (cntrl(String.sub(s, i + 1)), i + 2)
	else (echar c, i + 1)
      end

    fun ccon s =	(* #\"{cdesc}\" -> char *)
      case String.sub(s,2)
	of #"\\" => let val (c, _) = escseq(s, 3) in c end
	 | c => c

    fun scon s =	(* \"{cdesc}*\" -> string *)
      let fun sitem(i, rev_cs) =
	    case String.sub(s,i)
	      of #"\""	=> String.implode(List.rev rev_cs)
	       | #"\\"	=>
		  let val (c, i) = escseq(s, i + 1)
		  in
		    sitem(i, c :: rev_cs)
		  end
	       | c	=> sitem(i + 1, c :: rev_cs)
      in
	sitem(1, [])
      end
*)
  end (* structure LexUtil *)
