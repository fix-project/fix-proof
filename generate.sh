#!/bin/bash

# Usage: ./generate.sh
OUTPUT="wasm-proofs/Wasm-Proof/Init.thy"

echo "theory Init" > $OUTPUT
echo "  imports Host" >> $OUTPUT
echo "begin" >> $OUTPUT

echo "" >> $OUTPUT

./spec/interpreter/wasm -pisa coupon.wat >> $OUTPUT

echo "" >> $OUTPUT
echo "end" >> $OUTPUT
