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
structure Util : UTIL =
  struct

    fun bound([], _) = NONE
      | bound((key, attr) :: env, key') =
          if key = key' then SOME attr else bound(env, key')

    exception Lookup

    fun lookup(env, key) =
      case bound(env, key)
       of SOME attr => attr
        | NONE => raise Lookup

    fun min(x, y) : int = if x < y then x else y

    fun member(_, []) = false
      | member(x, y :: ys) = (x = y) orelse member(x, ys)

    fun intersect'([], _, zs) = zs
      | intersect'(x :: xs, ys, zs) =
        intersect'(xs, ys, if member(x, ys) then x :: zs else zs)

    fun intersect(xs, ys) = intersect'(xs, ys, [])

    fun after(compute, cleanup) =
      let datatype 'a status = OK of 'a | EXN of exn
	  val status = OK(compute()) handle exn => EXN exn
	  val _ = cleanup()
      in
	case status
	 of OK value => value
	  | EXN exn => raise exn
      end

  end
