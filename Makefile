.DEFAULT_GOAL := all
.PHONY: all check check-full check-generated clean rocq rocq-check rocq-init

all: rocq

check: rocq-check

check-full:
	$(MAKE) -C wasm-proofs/rocq check-full

check-generated:
	$(MAKE) -C wasm-proofs/rocq check-generated

clean:
	$(MAKE) -C wasm-proofs/rocq clean

rocq-init:
	python3 scripts/generate-rocq-init.py

rocq:
	$(MAKE) -C wasm-proofs/rocq

rocq-check:
	$(MAKE) -C wasm-proofs/rocq check
