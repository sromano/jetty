all:
	ocamlopt  -inline 100 -ffast-math unix.cmxa -thread threads.cmxa -o test utils.ml type.ml expression.ml task.ml library.ml enumerate.ml compress.ml ec.ml em.ml phonetics.ml  symbolic_dimensionality_reduction.ml polynomial.ml  #morphology.ml #-unsafe  bottom_up.ml 
clean:
	rm test *.cmi *.cmo *cmx *~ 
run:
	./test | tee log/output
