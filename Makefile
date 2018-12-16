.PHONY: all test-all lib clean

all: \
	exe/day01_1 exe/day01_2 \
	exe/day02_1 exe/day02_2 \
	exe/day03_1 exe/day03_2 \
	exe/day04_1 \
	exe/day05_1 exe/day05_2 \
	exe/day07_1 exe/day07_2 \
	exe/day09_1 \
	exe/day10_1 \
	exe/day16_1

exe:
	mkdir exe/

test-all: all
	./exe/day01_1 < ./txt/day01
	@echo "3         < Expected output"
	./exe/day01_2 < ./txt/day01
	@echo "2         < Expected output"
	./exe/day02_1 < ./txt/day02
	@echo "12        < Expected output"
	./exe/day02_1 < ./txt/day02.bis
	./exe/day02_2 < ./txt/day02
	./exe/day02_2 < ./txt/day02.bis
	@echo "fgij      < Expected output"
	./exe/day03_1 < ./txt/day03
	@echo "4         < Expected output"
	./exe/day03_2 < ./txt/day03
	@echo "3         < Expected output"
	./exe/day04_1 < ./txt/day04
	@echo "240       < Expected output"
	@echo "TODO day04_2"
	@echo "4455      < Expected output"
	./exe/day05_1 < ./txt/day05
	@echo "10        < Expected output"
	./exe/day05_2 < ./txt/day05
	@echo "4         < Expected output"
	./exe/day07_1 < ./txt/day07
	@echo "CABDFE    < Expected output"
	./exe/day07_2 < ./txt/day07
	@echo "253       < Expected output"
	./exe/day09_1 < ./txt/day09
	@echo "32        < Expected output"
	echo -e "3\n0\n10\n0\n8"|cat - txt/day10|./exe/day10_1
	@echo "(Should spell HI)"

lib: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

exe/%: exe sol/%.vo
	ocamlopt -I sol/ sol/$*.mli sol/$*.ml -o $@

.PRECIOUS: sol/%.vo
sol/%.vo: lib sol/%.v
	cd sol/ ; coqc -Q .. advent $*.v

sol/day05_1.vo sol/day05_2.vo: sol/day05_common.vo

# ln -s _CoqConfig.append _CoqConfig.extras
_CoqConfig.append:
	touch $@

_CoqProject: _CoqConfig _CoqConfig.append
	cat _CoqConfig _CoqConfig.append > _CoqProject

clean:
	$(RM) -r exe/
	$(RM) sol/day*.ml{i,} {*,.}/*.{glob,vo,cmi,cmx,cmo,o} {*,.}/.*.aux {*,.}/.lia.cache .coqdeps.d Makefile.coq Makefile.coq.conf
