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

    in

      datatype ('key, 'value) dict
	= DICT of {compare: 'key * 'key -> order,
		   tree: ('key, 'value) tree}

      fun empty compare = DICT{compare = compare, tree = E}

      fun insert(DICT{compare, tree}, x, y) =
	DICT{compare = compare, tree = tinsert(compare, tree, x, y)}

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
