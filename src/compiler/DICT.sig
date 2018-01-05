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
 *)
signature DICT =
  sig

    (* structure Key : ORD_KEY *)	(* XXX: TODO *)

    type ('key, 'value) dict

    val empty	: ('key * 'key -> order) -> ('key, 'value) dict
    val insert	: ('key, 'value) dict * 'key * 'value -> ('key, 'value) dict
    val find'	: ('key, 'value) dict * 'key -> ('key * 'value) option
    val find	: ('key, 'value) dict * 'key -> 'value option
    val plus	: ('key, 'value) dict * ('key, 'value) dict -> ('key, 'value) dict
    val fold	: ('key * 'value * 'b -> 'b) * 'b * ('key, 'value) dict -> 'b
    val fromList: ('key * 'key -> order) * ('key * 'value) list -> ('key, 'value) dict

  end (* signature DICT *)
