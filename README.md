# Fix coupon proofs

This repository proves the Fix evaluation and coupon rules in Rocq, and proves
that the constructors in `coupon.wat` return good coupons or trap as specified.
The development uses Rocq 9.1.1 and
[WasmCert-Coq](https://github.com/WasmCert/WasmCert-Coq), pinned to commit
`5e6df8d60c94aa5dbeff633f5eb48caa6c64c225` (package version 2.2.1).

The 35 proof modules are in `wasm-proofs/rocq`. They retain the development's
structure: handles, evaluation, congruence, coinductive equivalence, equivalence
closure, coupon judgements, guarded constructors, and Wasm execution.
[STATUS.md](wasm-proofs/rocq/STATUS.md) records coverage and verification;
[CORRESPONDENCE.md](wasm-proofs/rocq/CORRESPONDENCE.md) explains the Isabelle-to-Rocq
translations and assumptions.

Install opam, Python 3, and WABT (`wat2wasm`), then run from this directory:

```sh
git submodule update --init --recursive
opam pin add -yn coq-wasm wasm-proofs/WasmCert-Coq
opam install . --deps-only -y
opam exec -- make
opam exec -- make check
```

`make` compiles the Rocq proofs. `make check` also checks generated-byte
freshness and runs `coqchk` over every proof module. CI runs this check.
`make clean` removes generated build artifacts. The `rocq`, `rocq-check`, and
`rocq-init` targets remain available for explicit invocation.

After editing `coupon.wat`, regenerate its representation with
`make rocq-init`. The generator wraps its module fields for WABT, compiles them
to Wasm bytes, and emits `Init.v`. Rocq parses those exact bytes and proves
parser success, module typing, function bodies, exports, and dispatch indices.
A stale generated file fails `make check`; unchanged generation preserves its
modification time to avoid rebuilding the proof unnecessarily.

Execution theorems use WasmCert-Coq's finite reduction semantics. Tree execution
states the original i32 size restrictions as explicit premises. The storage,
program, coupon-storage, and externref backends remain abstract interfaces;
their contracts and standard logical assumptions are documented in the
correspondence audit.
