.PHONY: all check check-full check-generated clean

CHECK_JOBS ?= 1

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
	python3 ../../scripts/check-rocq.py --jobs $(CHECK_JOBS)

check-full: check-generated
	$(MAKE) all
	python3 ../../scripts/check-rocq.py --force --jobs $(CHECK_JOBS)

clean: CoqMakefile
	$(MAKE) -f CoqMakefile clean
	rm -rf .rocq-check-cache
