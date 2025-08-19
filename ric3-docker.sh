#!/bin/bash
# This script runs the rIC3 binary inside a minimal Docker container.
# It mounts the current working directory to /work in the container,
# so you can use it as if you were running the binary natively.

docker run --rm -it \
  -v "$(pwd)":/work \
  -w /work \
  alpine:latest \
  ./target/x86_64-unknown-linux-musl/release/rIC3 "$@"
