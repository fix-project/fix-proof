# A base image with Isabelle2025-2, latest AFP, and opam dependencies for spec/interpreter

FROM makarius/isabelle:Isabelle2025-2

USER root
RUN adduser ubuntu isabelle

USER ubuntu
WORKDIR /home/ubuntu

ENV PATH="/home/isabelle/Isabelle/bin:${PATH}"

# install afp
RUN curl -L -o afp-current.tar.gz "https://isa-afp.org/release/afp-current.tar.gz" && \
    afptopdir=$(tar -tzf afp-current.tar.gz | head -1 | cut -d/ -f1) && \
    tar -xzf afp-current.tar.gz && \
    isabelle components -u ${afptopdir}/thys

# install opam
USER root
RUN apt-get update && \
    apt-get install -y opam
USER ubuntu

RUN opam init \
        --disable-sandboxing \
        --no-setup \
        --yes \
    && opam env --switch=default

# Setup opam for building spec
RUN opam switch create 4.11.2 && \
    opam env --switch=4.11.2

RUN opam install ocamlbuild -y

USER root
RUN apt-get install -y libgmp-dev pkg-config
USER ubuntu

RUN opam install zarith -y

ENV PATH="/home/ubuntu/.opam/4.11.2/bin:${PATH}"

USER root
RUN chmod 1777 /tmp/isabelle-
USER ubuntu
