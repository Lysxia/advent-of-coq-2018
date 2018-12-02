.PHONY: lib

lib: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

%.native: lib %.v
	coqc $(shell cat _CoqProject) $*.v
	ocamlc $*.mli $*.ml -o $@
