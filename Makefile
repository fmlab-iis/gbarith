MODULES := \
	src/utile.ml \
	src/entiers.ml \
	src/polynomes2.ml \
	src/dansideal.ml \
	src/gbarith_compute.mli \
	src/gbarith_compute.ml \
	src/gbarith_tactic.ml4 \
	src/gbarith_plugin_mod.ml \
	src/gbarith_plugin.mllib \
	src/GBCompute.v \
	src/GBR.v \
	src/GBZ.v \
	src/GBZArith.v \
#	test-suite/GBExamples.v
NAME := GBArith
ROOT := ./
.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(MODULES)
	coq_makefile \
	-I $(ROOT)src \
	-R $(ROOT)src $(NAME) \
	$(MODULES) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
