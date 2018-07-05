(*
 * Copyright 1996, 2015-2018 Mikael Pettersson
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
 * De-functorized version of:
 *
 * aa-dict-fn.sml
 * Written by: Mikael Pettersson, 1996.
 *
 * An SML implementation of dictionaries based on balanced search
 * trees as described in the following article:
 *
 * @InProceedings{Andersson93,
 *  author =	{Arne Andersson},
 *  title =	{Balanced Search Trees Made Simple},
 *  pages =	{60--71},
 *  crossref =	{WADS93}
 * }
 *
 * @Proceedings{WADS93,
 *   title =	{Proceedings of the Third Workshop on Algorithms and Data Structures, WADS'93},
 *   booktitle ={Proceedings of the Third Workshop on Algorithms and Data Structures, WADS'93},
 *   editor =	{F. Dehne and J-R. Sack and N. Santoro and S. Whitesides},
 *   publisher ={Springer-Verlag},
 *   series =	{Lecture Notes In Computer Science},
 *   volume =	709,
 *   year =	1993
 * }
 *
 * The original Pascal code represented empty trees by a single shared node
 * with level 0, and whose left and right fields pointed back to itself.
 * The point of this trick was to eliminate special cases in the skew and
 * split procedures. Since it would be expensive to emulate, this SML code
 * uses a traditional representation, making all special cases explicit.
 *
 * This is the vanilla version with no optimizations applied.
 *
 * Code for deletion based on:
 * "P. Ragde, Simple Balanced Binary Search Trees, Trends in Functional Programming
 * in Education (TFPIE 2014), EPTCS 170, 2014, pp. 78--87.
 *)
structure Dict : DICT =
  struct

    local

      datatype ('key, 'value) tree
	= E
	| T of {key: 'key,
		attr: 'value,
		level: int,
		left: ('key, 'value) tree,
		right: ('key, 'value) tree	}

      (* Transform
       *
       *    x -> y -> z       level
       *   /    /    / \
       *  a    b    c   d     level - 1
       *
       * into
       *
       *        y             level + 1
       *       / \
       *      /   \
       *     x     z          level
       *    / \   / \
       *   a   b c   d        level - 1
       *)
      fun split(t as E) = t
	| split(t as T{right=E,...}) = t
	| split(t as T{right=T{right=E,...},...}) = t
	| split(t as T{key=kx,attr=ax,level=lx,left=a,
		       right=T{key=ky,attr=ay,left=b,
			       right=(z as T{level=lz,...}),...}}) =
	    if lx = lz then	(* rotate left *)
	      T{key=ky,attr=ay,level=lx+1,right=z,
		left=T{key=kx,attr=ax,level=lx,left=a,right=b}}
	    else t

      (* Transform
       *
       *    y <- x            level
       *   / \    \
       *  a   b    c          level - 1
       *
       * into
       *
       *    y -> x            level
       *   /    / \
       *  a    b   c          level - 1
       *)
      fun skew(t as E) = t
	| skew(t as T{left=E,...}) = t
	| skew(t as T{key=kx,attr=ax,level=lx,right=c,
		      left=T{key=ky,attr=ay,level=ly,left=a,right=b}}) =
	    if lx = ly then	(* rotate right *)
	      T{key=ky,attr=ay,level=ly,left=a,
		right=T{key=kx,attr=ax,level=lx,left=b,right=c}}
	    else t

      fun tfind(compare, t, x) =
	let fun look(E) = E
	      | look(t as T{key,left,right,...}) =
		  case compare(x, key)
		    of LESS => look left
		     | GREATER => look right
		     | EQUAL => t
	in
	  look t
	end

      fun tinsert(compare, t, x, y) =
        let fun insert'(E, x, y) = T{key=x, attr=y, level=1, left=E, right=E}
	      | insert'(T{key,attr,level,left,right}, x, y) =
		let val t = case compare(x,key)
			      of LESS =>
				 T{key=key, attr=attr, level=level, right=right,
				   left=insert'(left,x,y)}
			       | GREATER =>
				 T{key=key, attr=attr, level=level, left=left,
				   right=insert'(right,x,y)}
			       | EQUAL =>
				 T{key=x, attr=y, level=level, left=left, right=right}
		    val t = skew t
		    val t = split t
		in
		  t
		end
	in
	  insert'(t, x, y)
	end

      fun tdelete(compare, t, x) =
	let fun dellrg(T{left=lt, key=kt, attr=at, right=E, ...}) = (lt, kt, at)
	      | dellrg(T{level=lv, left=lt, key=kt, attr=at, right=rt}) =
		let val (lt', k', a') = dellrg lt
		in
		  (T{level=lv, left=lt', key=kt, attr=at, right=rt}, k', a')
		end
	      | dellrg(E) = raise Match (* silence non-exhaustive warning *)
	    fun level(E) = 0
	      | level(T{level=lvt,...}) = lvt
	    fun sngl(E) = false
	      | sngl(T{right=E,...}) = true
	      | sngl(T{level=lvx, right=T{level=lvy,...}, ...}) = lvx > lvy
	    fun nlvl(t as T{level=lvt, ...}) = if sngl t then lvt - 1 else lvt
	      | nlvl(E) = raise Match (* silence non-exhaustive warning *)
	    fun adjust(t as T{level=lvt, left=lt, key=kt, attr=at, right=rt}) =
		  if (level lt >= lvt-1) andalso (level rt >= lvt-1) then
		    t
		  else if (level rt < lvt-1) andalso sngl lt then
		    skew(T{level=lvt-1, left=lt, key=kt, attr=at, right=rt})
		  else if (level rt < lvt-1) then
		    case lt
		      of T{level=lvl, left=a, key=kl, attr=al, right=T{level=lvb, left=lb, key=kb, attr=ab, right=rb}} =>
			   T{level=lvb+1, key=kb, attr=ab,
			     left=T{level=lvl, left=a, key=kl, attr=al, right=lb},
                             right=T{level=lvt-1, left=rb, key=kt, attr=at, right=rt}}
		       | _ => raise Match (* silence non-exhaustive warning *)
		  else if (level rt < lvt) then
		    split(T{level=lvt-1, left=lt, key=kt, attr=at, right=rt})
		  else
		    (case rt
		       of T{level=lvr, left=(a as T{level=lva, left=c, key=ka, attr=aa, right=d}), key=kr, attr=ar, right=b} =>
			    T{level=lva+1, key=ka, attr=aa,
			      left=T{level=lvt-1, left=lt, key=kt, attr=at, right=c},
			      right=split(T{level=nlvl a, left=d, key=kr, attr=ar, right=b})}
			| _ => raise Match) (* silence non-exhaustive warning *)
	      | adjust(E) = raise Match (* silence non-exhaustive warning *)
	    fun delete(k, t) =
	      case t
		of E => E
		 | T{level=lvt, left=lt, key=kt, attr=at, right=rt} =>
		     case compare(k, kt)
		       of LESS =>
			    adjust(T{level=lvt, left=delete(k, lt), key=kt, attr=at, right=rt})
			| GREATER =>
			    adjust(T{level=lvt, left=lt, key=kt, attr=at, right=delete(k, rt)})
			| EQUAL =>
			    case (lt, rt)
			      of (E, _) => rt
			       | (_, E) => lt
			       | (_, _) =>
				   let val (lt', k', a') = dellrg lt
				   in
				     adjust(T{level=lvt, left=lt', key=k', attr=a', right=rt})
				   end
	in
	  delete(x, t)
	end

    in

      datatype ('key, 'value) dict
	= DICT of {compare: 'key * 'key -> order,
		   tree: ('key, 'value) tree}

      fun empty compare = DICT{compare = compare, tree = E}

      fun isEmpty(DICT{tree = E, ...}) = true
	| isEmpty(_) = false

      fun insert(DICT{compare, tree}, x, y) =
	DICT{compare = compare, tree = tinsert(compare, tree, x, y)}

      fun delete(DICT{compare, tree}, x) =
	DICT{compare = compare, tree = tdelete(compare, tree, x)}

      fun find'(DICT{compare, tree}, x) =
	case tfind(compare, tree, x)
	  of E => NONE
	   | T{key,attr,...} => SOME(key,attr)

      fun find(DICT{compare, tree}, x) =
	case tfind(compare, tree, x)
	  of E => NONE
	   | T{attr,...} => SOME attr

      fun plus(DICT{compare, tree}, DICT{tree = tree2, ...}) =
	let fun plus'(bot, E) = bot
	      | plus'(bot, T{key,attr,left,right,...}) =
		tinsert(compare, plus'(plus'(bot, left), right), key, attr)
	in
	  DICT{compare = compare, tree = plus'(tree, tree2)}
	end

      fun fold(f, init, DICT{tree = dict, ...}) =
	let fun traverse(E, state) = state
	      | traverse(T{key,attr,left,right,...}, state) =
		  traverse(right, traverse(left, f(key,attr,state)))
	in
	  traverse(dict, init)
	end

      fun fromList(compare, alist) =
	let fun insert((x, y), t) = tinsert(compare, t, x, y)
	in
	  DICT{compare = compare, tree = List.foldl insert E alist}
	end

    end (* local *)

  end (* structure Dict *)
