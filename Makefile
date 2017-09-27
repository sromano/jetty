c = corebuild

Chinese:
	$(c) crp.native; cp crp.native test

type:
	$(c) type.native; cp type.native test
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
run:
	./test | tee log/output
