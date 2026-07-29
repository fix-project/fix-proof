.PHONY: all

all: thy
	isabelle build -D wasm-proofs -v Wasm-Proof

wasm-proofs/Wasm-Proof/Init.thy: coupon.wat generate.sh interpreter
	./generate.sh

thy: wasm-proofs/Wasm-Proof/Init.thy

interpreter:
	$(MAKE) -C spec/interpreter



