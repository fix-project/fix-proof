.PHONY: all check check-generated clean

MODULES := $(patsubst %.v,FixProof.%,$(filter %.v,$(shell cat _CoqProject)))

all: Init.v CoqMakefile
	$(MAKE) -f CoqMakefile all

Init.v: ../../coupon.wat ../../scripts/generate-rocq-init.py
	python3 ../../scripts/generate-rocq-init.py

CoqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o $@

check-generated:
	python3 ../../scripts/generate-rocq-init.py --check

# Check committed generated input before the build can regenerate it.
check: check-generated
	$(MAKE) all
	rocq check -silent -Q . FixProof $(MODULES)

clean: CoqMakefile
	$(MAKE) -f CoqMakefile clean
