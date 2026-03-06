#!/bin/bash

# Usage: ./generate.sh input.wat
OUTPUT="wasm-proofs/Wasm-Proof/Init.thy"

echo "theory Init" > $OUTPUT
echo "  imports Host" >> $OUTPUT
echo "begin" >> $OUTPUT

echo "" >> $OUTPUT

./spec/interpreter/wasm -pisa $1 >> $OUTPUT

echo "" >> $OUTPUT
echo "end" >> $OUTPUT
