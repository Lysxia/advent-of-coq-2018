.PHONY: all test-all lib clean

all: day01_1.native day01_2.native \
	day02_1.native day02_2.native \
	day03_1.native day03_2.native \
	day04_1.native \
	day05_1.native day05_2.native

test-all: all
	./day01_1.native < day01.example
	./day01_2.native < day01.example
	./day02_1.native < day02.example
	./day02_1.native < day02.example.bis
	./day02_2.native < day02.example
	./day02_2.native < day02.example.bis
	./day03_1.native < day03.example
	./day03_2.native < day03.example
	./day04_1.native < day04.example
	./day05_1.native < day05.example
	./day05_2.native < day05.example

lib: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

%.native: lib %.v
	coqc -Q . advent $*.v
	ocamlc $*.mli $*.ml -o $@

clean:
	$(RM) **/*.glob **/*.vo *.glob *.vo *.cmi *.cmo day*.ml day*.mli *.native Makefile.coq Makefile.coq.conf
