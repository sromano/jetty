all:
	ocamlopt unix.cmxa -thread threads.cmxa -o test utils.ml type.ml expression.ml library.ml enumerate.ml task.ml em.ml compress.ml # polynomial.ml
