.PHONY: all

all: thy
	isabelle build -D wasm-proofs -v Wasm-Proof
	

wasm-proofs/Wasm-Proof/Init.thy: coupon.wat generate.sh
	./generate.sh

thy: wasm-proofs/Wasm-Proof/Init.thy



