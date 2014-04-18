all:
	ocamlopt -o test utils.ml type.ml expression.ml library.ml enumerate.ml
