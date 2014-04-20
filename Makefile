all:
	ocamlopt -o test unix.cmxa utils.ml type.ml expression.ml library.ml enumerate.ml task.ml em.ml polynomial.ml
