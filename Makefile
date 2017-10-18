c = corebuild

Chinese:
	$(c) crp.native; cp crp.native test

type:
	$(c) type.native; cp type.native test
%: %.ml
	$(c) $@.native; cp $@.native test
morphology:
	$(c) morphology.native; cp morphology.native test
lambda:
	$(c) lambda_calculus.native; cp lambda_calculus.native test
polynomial:
	$(c) polynomial.native; cp polynomial.native test
xor:
	$(c) xor.native; cp xor.native test
regress:
	$(c) regress.native; cp regress.native test
clean:
	rm -rf _build test
toplevel:
	ocamlfind ocamlmktop -o play -linkpkg -package core,threads,csv -thread _build/type.cmo _build/utils.cmo _build/time_limit.cmo _build/expression.cmo _build/drawing.cmo _build/task.cmo _build/library.cmo _build/enumerate.cmo _build/compress.cmo _build/partial_evaluation.cmo _build/bottom_up.cmo _build/frontier.cmo _build/em.cmo _build/graphics.cmo ;\
	mv play _build/
run:
	./test | tee log/output
