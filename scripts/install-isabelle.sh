#!/bin/bash

curl -L -o isabelle.tar.gz "https://isabelle.in.tum.de/dist/Isabelle2025-2_linux.tar.gz"
isabelletopdir=$(tar -tzf isabelle.tar.gz | head -1 | cut -d/ -f1)
tar -xzf isabelle.tar.gz

curl -L -o afp-current.tar.gz "https://isa-afp.org/release/afp-current.tar.gz"
afptopdir=$(tar -tzf afp-current.tar.gz | head -1 | cut -d/ -f1)
tar -xzf afp-current.tar.gz

export PATH=$PATH:$(pwd)/${isabelletopdir}/bin
isabelle components -u ${afptopdir}/thys

