all:
	ocamlopt  -inline 100 -ffast-math unix.cmxa -thread threads.cmxa -o test utils.ml type.ml expression.ml task.ml library.ml enumerate.ml compress.ml ec.ml em.ml polynomial.ml #-unsafe 
clean:
	rm test *.cmi *.cmo *cmx *~ 
run:
	./test
