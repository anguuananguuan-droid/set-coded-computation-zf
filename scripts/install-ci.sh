#!/usr/bin/env bash
# Pinned Linux dependencies for the public proof build.
set -euo pipefail

deps_dir="${1:?usage: install-ci.sh DEPENDENCY_DIRECTORY}"
mkdir -p "$deps_dir"
cd "$deps_dir"

if [[ ! -x Isabelle2025-2/bin/isabelle ]]; then
  curl --fail --location --retry 3 \
    https://isabelle.in.tum.de/website-Isabelle2025-2/dist/Isabelle2025-2_linux.tar.gz \
    --output isabelle.tar.gz
  echo 'a20a507bc7c1270d8be96a9f3fbec06345387789d2dc2c4d3df6260d47bfb33c  isabelle.tar.gz' | sha256sum --check
  tar -xzf isabelle.tar.gz
  rm isabelle.tar.gz
fi

if [[ ! -f afp-2026-02-06/ROOTS ]]; then
  curl --fail --location --retry 3 \
    https://isa-afp.org/release/afp-2026-02-06.tar.gz \
    --output afp.tar.gz
  echo 'b059edd46073479ee8dde45004c2346a7365e5d94cded49d27257cfea66c8879  afp.tar.gz' | sha256sum --check
  tar -xzf afp.tar.gz
  rm afp.tar.gz
fi
