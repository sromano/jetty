c = corebuild

morphology:
	$(c) morphology.native; cp morphology.native test
polynomial:
	$(c) polynomial.native; cp polynomial.native test
regress:
	$(c) regress.native; cp regress.native test
clean:
	rm -rf _build test
run:
	./test | tee log/output
