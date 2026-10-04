.DEFAULT_GOAL := all
.PHONY: all check clean rocq rocq-check rocq-init

all: rocq

check: rocq-check

clean:
	$(MAKE) -C wasm-proofs/rocq clean

rocq-init:
	python3 scripts/generate-rocq-init.py

rocq:
	$(MAKE) -C wasm-proofs/rocq

rocq-check:
	$(MAKE) -C wasm-proofs/rocq check
