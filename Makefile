%.native: %.v
	coqc $(shell cat _CoqProject) $*.v
	ocamlc $*.mli $*.ml -o $@
