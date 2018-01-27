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
signature UTIL =
  sig
    val bound		: (''a * 'b) list * ''a -> 'b option
    val lookup		: (''a * 'b) list * ''a -> 'b (* XXX: delete *)
    val min		: int * int -> int
    val member		: ''a * ''a list -> bool
    val intersect	: ''a list * ''a list -> ''a list
    val sort		: ('a * 'a -> bool) * 'a list -> 'a list
    val after		: (unit -> 'a) * (unit -> unit) -> 'a
  end
