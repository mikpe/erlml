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

MODULES=\
	TextIO \
	_ERLML_PRIMITIVE \
	erlml_runtime

BEAM_FILES=$(MODULES:%=%.beam)

.SUFFIXES: .erl .beam

%.beam: %.erl
	erlc $<

beams:	$(BEAM_FILES)

clean:
	rm -f $(BEAM_FILES)
