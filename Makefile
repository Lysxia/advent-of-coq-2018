.PHONY: all lib

all: day01_1.native day01_2.native

test-all: all
	./day01_1.native < day01.example
	./day01_2.native < day01.example

lib: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

%.native: lib %.v
	coqc -Q . advent $*.v
	ocamlc $*.mli $*.ml -o $@
