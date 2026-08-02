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

# Packaging and sharing local Isabelle heap

To speed up the github action, you could choose to package your local Isabelle heap image. After building the whole project:

```bash
cd scripts
./package-heap-cache.sh
```
The script pushes a docker image to `ghcr.io/fix-project`, and make sure the credentials are setup properly before running the script.

Record the built docker image tag, and add
```
Isabelle-Cache: $IMAGETAG
```
to the end of your commit message.

The generated heap images could only be used if the relative path of the project directory to your `$HOME` is `$HOME/fix-proof`. If that's not the case, include the relative path in your commit message as:

```
Workdir: $RELATIVEPATH
```
