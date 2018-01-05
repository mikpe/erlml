%%% -*- erlang-indent-level: 2 -*-
%%%
%%% Copyright 2018 Mikael Pettersson
%%%
%%% Licensed under the Apache License, Version 2.0 (the "License");
%%% you may not use this file except in compliance with the License.
%%% You may obtain a copy of the License at
%%%
%%%     http://www.apache.org/licenses/LICENSE-2.0
%%%
%%% Unless required by applicable law or agreed to in writing, software
%%% distributed under the License is distributed on an "AS IS" BASIS,
%%% WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
%%% See the License for the specific language governing permissions and
%%% limitations under the License.

-module(erlml_runtime).
-export([ init/0
        , set_var/2
        , get_var/1
        , raise_match/0
        ]).

init() -> ets:new(?MODULE, [named_table, public]).

set_var(Key, Val) -> ets:insert(?MODULE, {Key, Val}), {}.

get_var(Key) -> ets:lookup_element(?MODULE, Key, 2).

raise_match() -> throw('Match').
