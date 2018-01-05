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
signature CORE_ERLANG =
  sig

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

    val mkVar: string option -> var

    (* convert basic entities to Core Erlang notation *)

    val integerToString: integer -> string
    val floatToString: float -> string
    val atomToString: atom -> string
    val stringToString: string -> string
    val varToString: var -> string

  end
