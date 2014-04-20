all:
	ocamlopt -thread -o test unix.cmxa threads.cmxa utils.ml type.ml expression.ml library.ml enumerate.ml task.ml em.ml
