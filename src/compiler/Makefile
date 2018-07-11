#
# Copyright 2018 Mikael Pettersson
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# Moscow ML specific Makefile for the ErlML compiler

UNITS=\
	UTIL.sig \
	Util \
	DICT.sig \
	Dict \
	SOURCE.sig \
	Source \
	LEXARG.sig \
	LexArg \
	TOKEN.sig \
	Token \
	LEXUTIL.sig \
	LexUtil \
	LEXER.sig \
	Lexer \
	TYPES.sig \
	Types \
	BASIS.sig \
	Basis \
	ABSYN.sig \
	Absyn \
	PARSER.sig \
	Parser \
	UNIFY.sig \
	Unify \
	EXPLICIT_TYVAR_SCOPE.sig \
	ExplicitTyVarScope \
	TYPE_CHECK.sig \
	TypeCheck \
	CORE_ERLANG.sig \
	CoreErlang \
	CORE_ERLANG_PRINT.sig \
	CoreErlangPrint \
	TRANSLATE.sig \
	Translate \
	MAIN.sig \
	Main \
	START.sig \
	Start \
	StartMosml

OFILES=$(UNITS:%=%.uo)
IFILES=$(UNITS:%=%.ui)

.SUFFIXES: .ui .uo

%.sig.uo %.sig.ui: %.sig
	if [ -L $<.sml ]; then rm $<.sml; fi
	ln -s $< $<.sml
	mosmlc -c -toplevel `echo $^ | sed s,$<,,` $<.sml
	if [ -L $<.sml ]; then rm $<.sml; fi

%.uo %.ui: %.sml
	mosmlc -c -toplevel `echo $^ | sed s,$<,,` $<

erlml2core: $(OFILES)
	mosmlc -toplevel -o $@ $^

ABSYN.sig.ui ABSYN.sig.uo: Basis.ui
Absyn.ui Absyn.uo: ABSYN.sig.ui Basis.ui
BASIS.sig.ui BASIS.sig.uo: Dict.ui Types.ui
Basis.ui Basis.uo: BASIS.sig.ui Dict.ui Util.ui Types.ui
CoreErlang.ui CoreErlang.uo: CORE_ERLANG.sig.ui
CORE_ERLANG_PRINT.sig.ui CORE_ERLANG_PRINT.sig.uo: CoreErlang.ui
CoreErlangPrint.ui CoreErlangPrint.uo: CORE_ERLANG_PRINT.sig.ui CoreErlang.ui Util.ui
Dict.ui Dict.uo: DICT.sig.ui
EXPLICIT_TYVAR_SCOPE.sig.ui EXPLICIT_TYVAR_SCOPE.sig.uo: Absyn.ui
ExplicitTyVarScope.ui ExplicitTyVarScope.uo: EXPLICIT_TYVAR_SCOPE.sig.ui Absyn.ui Dict.ui Basis.ui
LEXARG.sig.ui LEXARG.sig.uo: Source.ui
LexArg.ui LexArg.uo: LEXARG.sig.ui Source.ui
LexUtil.ui LexUtil.uo: LEXUTIL.sig.ui
LEXER.sig.ui LEXER.sig.uo: LexArg.ui Token.ui
Lexer.ui Lexer.uo: LEXER.sig.ui LexArg.ui Token.ui LexUtil.ui
Main.ui Main.uo: MAIN.sig.ui Parser.ui TypeCheck.ui Absyn.ui Basis.ui Translate.ui CoreErlangPrint.ui
PARSER.sig.ui PARSER.sig.uo: LexArg.ui Absyn.ui
Parser.ui Parser.uo: PARSER.sig.ui Token.ui LexArg.ui Lexer.ui Absyn.ui Dict.ui Basis.ui Util.ui
Source.ui Source.uo: SOURCE.sig.ui
Start.ui Start.uo: START.sig.ui Main.ui
StartMosml.ui StartMosml.uo: Start.ui
Token.ui Token.uo: TOKEN.sig.ui
TRANSLATE.sig.ui TRANSLATE.sig.uo: Absyn.ui CoreErlang.ui
Translate.ui Translate.uo: TRANSLATE.sig.ui Absyn.ui CoreErlang.ui Basis.ui Dict.ui
TYPE_CHECK.sig.ui TYPE_CHECK.sig.uo: Absyn.ui Basis.ui
TypeCheck.ui TypeCheck.uo: TYPE_CHECK.sig.ui Basis.ui Dict.ui Absyn.ui Util.ui ExplicitTyVarScope.ui Types.ui
Types.ui Types.uo: TYPES.sig.ui Util.ui
UNIFY.sig.ui UNIFY.sig.uo: Types.ui
Unify.ui Unify.uo: UNIFY.sig.ui Types.ui Util.ui
Util.ui Util.uo: UTIL.sig.ui

clean:
	rm -f erlml2core $(OFILES) $(IFILES)
