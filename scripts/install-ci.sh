#!/usr/bin/env bash
# Pinned Linux dependencies for the public proof build.
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
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

if [[ ! -f afp-2026-10-06/thys/ROOTS ]]; then
  curl --fail --location --retry 3 \
    https://isa-afp.org/release/afp-2026-10-06.tar.gz \
    --output afp.tar.gz
  echo 'd6f917ba347c5f8aa5b3b0b95686edc96c8d977dcaed4bd01e6fa555d450996e  afp.tar.gz' | sha256sum --check
  tar -xzf afp.tar.gz
  rm afp.tar.gz
fi

linter_revision=c9983adc5c51a6455f702bb58c9f960d425a2af3
if [[ ! -f "isabelle-linter-$linter_revision/linter_base/src/linter.scala" ]]; then
  curl --fail --location --retry 3 \
    "https://codeload.github.com/isabelle-prover/isabelle-linter/tar.gz/$linter_revision" \
    --output linter.tar.gz
  echo '83dc386d6e9dcbfa9f820abddac31c1bedffa46f1f74265a8ccf9007ff9ca2f1  linter.tar.gz' | sha256sum --check
  tar -xzf linter.tar.gz
  rm linter.tar.gz
fi

python3 "$script_dir/patch_isabelle_linter.py" "isabelle-linter-$linter_revision"
