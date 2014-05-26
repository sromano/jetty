base = utils.ml type.ml expression.ml task.ml library.ml enumerate.ml compress.ml partial_evaluation.ml  bottom_up.ml frontier.ml em.ml ec.ml  symbolic_dimensionality_reduction.ml phonetics.ml

c = ocamlopt  -inline 100 -ffast-math unix.cmxa -thread threads.cmxa

morphology:
	$(c) -o test $(base) morphology.ml
polynomial:
	$(c) -o test $(base) polynomial.ml
test:
	$(c) -o test $(base) 
clean:
	rm test *.cmi *.cmo *cmx *~ 
run:
	./test | tee log/output
