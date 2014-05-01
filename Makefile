all:
	ocamlopt -ffast-math -inline 100 -p unix.cmxa -thread threads.cmxa -o test utils.ml type.ml expression.ml task.ml library.ml enumerate.ml compress.ml em.ml polynomial.ml #-unsafe
clean:
	rm *.cmi *.cmo *cmx *~ 
