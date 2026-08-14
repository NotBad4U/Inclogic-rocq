# Hand-written wrapper around the Makefile that `rocq makefile` generates from
# _CoqProject.  Only this file and _CoqProject are tracked in git; Makefile.coq,
# Makefile.coq.conf and .Makefile.coq.d are generated and bake in the absolute
# paths of the toolchain in use, so they are gitignored.
#
# Every target not listed below is forwarded to Makefile.coq, so `make`,
# `make -j4`, `make clean`, `make html`, `make install`, ... all work as usual.

COQBIN ?=
ifneq (,$(COQBIN))
COQBIN := $(COQBIN)/
endif
COQMKFILE ?= "$(COQBIN)rocq" makefile

# Targets handled here, never forwarded to Makefile.coq
KNOWNTARGETS := Makefile.coq
# Files that must not be mistaken for targets by the catch-all rule below
KNOWNFILES := Makefile _CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

Makefile.coq: _CoqProject
	$(COQMKFILE) -f _CoqProject -o Makefile.coq

invoke-coqmakefile: Makefile.coq
	$(MAKE) --no-print-directory -f Makefile.coq \
	  $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)

# This must stay the last rule: it catches every other target
%: invoke-coqmakefile
	@true
