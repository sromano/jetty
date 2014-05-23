all:
	ocamlopt  -inline 100 -ffast-math unix.cmxa -thread threads.cmxa -o test utils.ml type.ml expression.ml task.ml library.ml enumerate.ml compress.ml partial_evaluation.ml em.ml bottom_up.ml ec.ml  symbolic_dimensionality_reduction.ml phonetics.ml morphology.ml #-unsafe    polynomial.ml 
clean:
	rm test *.cmi *.cmo *cmx *~ 
run:
	./test | tee log/output
