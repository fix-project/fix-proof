# Environment setup

## Isabelle
This project requires Isabelle2025-2. As of Jun 2026, the installation instructions can be found [here](https://isabelle.in.tum.de/installation.html).

## Isabelle AFP
Download AFP [here](https://isa-afp.org/download/).

Assume that `isabelle` has been installed with `PATH` set properly, before building the project, add AFP to Isabelle:

```bash
tar -xvf afp-current.tar.gz
isabelle components -u ${EXTRACTED_AFP_DIR}/thys
```

See `scripts/install-isabelle.sh` for more info.

## spec
Build `spec/interpreter`. It requires installing OCaml ([instructions](https://ocaml.org/docs/installing-ocaml)). See `spec/interpreter/README.md` for more info.

# Workflow

## Update `coupon.wat`

After making changes to `coupon.wat`, run `generate.sh` to update the coupon ISA in Isabelle.

or

```bash
make thy
```

## Invoke jedit

```bash
isabelle jedit -d wasm-proofs
```

## Build from command line

```bash
isabelle build -D wasm-proofs -v Wasm-Proof
```

or

```bash
make
```
