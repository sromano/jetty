all:
	ocamlopt  -inline 100 -ffast-math unix.cmxa -thread threads.cmxa -o test utils.ml type.ml expression.ml task.ml library.ml enumerate.ml compress.ml partial_evaluation.ml bottom_up.ml ec.ml em.ml  symbolic_dimensionality_reduction.ml polynomial.ml phonetics.ml  #morphology.ml #-unsafe  
clean:
	rm test *.cmi *.cmo *cmx *~ 
run:
	./test | tee log/output
