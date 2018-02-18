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
 *)
signature BASIS =
  sig

    type ident        = string	(* TODO: for now *)
    val identCompare  : ident * ident -> order

    datatype longid   = LONGID of ident list * ident

    datatype idstatus = CON of bool (* hasarg? *)
		      | EXN of bool (* hasarg? *)
		      | VAL
    datatype valenv   = VE of (ident, idstatus) Dict.dict (* TODO: add TypeScheme *)

    datatype tystr    = TYSTR of Types.tyfcn * valenv
    datatype tyenv    = TE of (ident, tystr) Dict.dict

    datatype env      = E of strenv * tyenv * valenv
    and strenv        = SE of (ident, env) Dict.dict

    datatype sigma    = SIG of env (* TODO: add TyNameSet? *)
    datatype sigenv   = SIGE of (ident, sigma) Dict.dict

    datatype basis    = BASIS of sigenv * env (* TODO: add FunEnv *)

    (* map top-level VIds to the structures in which they are bound, and their status;
       for primitives we use the proxy structure $PRIMITIVE *)
    val toplevelValEnv : (ident, longid * idstatus) Dict.dict

    val emptyVE : valenv
    val emptyEnv : env
    val emptyBasis : basis
    val initialBasis : basis

    val write : string * basis -> unit
    val read : string -> basis

  end
