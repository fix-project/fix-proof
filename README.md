For Wasm Proof Playground:
1. Install Isabelle (https://isabelle.in.tum.de/installation.html)
2. Download AFP (https://www.isa-afp.org/download/)

For Linux and Mac:
Assuming you have downloaded and unzipped the afp to /home/myself/afp, run:
`isabelle components -u /home/myself/afp/thys`

4. run `isabelle build -D .` in /fix-proof/wasm-proof/WasmCert-Isabelle/WebAssembly/

gross:
If you are using the Isabelle editor and the Wasm_Proof_Playground proof is still red, try clicking on the necessary import files in /fix-proof/wasm-proofs/WasmCert-Isabelle/WebAssembly/
