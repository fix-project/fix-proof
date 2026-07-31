#!/bin/bash

# get isabelle heap address and git commit
ISABELLE_HEAPS=$(isabelle getenv -b ISABELLE_HEAPS)

# package heap images
tar --zstd -cf isabelle-heaps.tar.zst \
  -C ${ISABELLE_HEAPS} \
  .

CACHE_HASH="$(sha256sum isabelle-heaps.tar.zst | cut -c1-12)"

# build a docker image
docker build \
  --build-arg CACHE_FILE=isabelle-heaps.tar.zst \
  -t ghcr.io/fix-project/isabelle-cache:"$CACHE_HASH" \
  -f heapcacheimage \
  .

docker push ghcr.io/fix-project/isabelle-cache:"$CACHE_HASH"
