# erlml
erlml - an ML implementation for the Erlang/OTP VM

ErlML
=====

ErlML is an implementation of the ML programming language, running
on the Erlang/OTP virtual machine.

ErlML currently aims for SML'97 compatibility, in order to facilitate
bootstrapping, but will likely later evolve into a unique ML dialect
better suited for the Erlang/OTP VM.

ErlML is written in a subset of SML'97 (with runtime support written
in Erlang), and compiles SML'97 to Core Erlang and then to BEAM code.

Status
======

ErlML currently requires an SML'97 compiler for compiling itself.
Moscow ML 2.10 is known to work.

The generated Core Erlang code requires an Erlang/OTP installation for
compiling it to BEAM and then executing it.  OTP-20 is known to work.

Features:
- ErlML performs separate compilation of individual signatures and
  structures.  It persists derived information about these compilation
  units in .basis files, and fetches those automatically when unbound
  signatures or structures are referenced.  It is required that each
  source file contains exactly ONE signature (.sig file) or structure
  (.sml file) declaration with the same name as the source file (except
  for the .sig or .sml extension).
- Eventually ErlML will support interfacing with Erlang, but that is
  not yet implemented.

Omissions:
- functors are not supported, and may never be
- sub-structures are not supported, and may never be
- sharing constrains are not supported, and may never be
- exceptions are currently not SML-compliant
- support for the SML Basis Library is incomplete, but improving
- the type checker is incomplete, but improving
- no documentation yet
- no Makefile yet
