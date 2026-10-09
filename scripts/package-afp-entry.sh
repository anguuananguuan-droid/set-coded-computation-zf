#!/usr/bin/env bash
set -euo pipefail

repository=$(cd "$(dirname "$0")/.." && pwd)
case ${1:-core} in
  core)
    entry=Set_Coded_Computation_ZF
    source_dir="$repository/Turing_Machines_ZF/Core"
    ;;
  invariance)
    entry=Set_Coded_Invariance_ZF
    source_dir="$repository/Set_Coded_Invariance_ZF"
    ;;
  *)
    printf 'usage: %s {core|invariance} [archive-path]\n' "$0" >&2
    exit 2
    ;;
esac
destination=${2:-"$repository/$entry.tar.gz"}
temporary=$(mktemp -d)
trap 'rm -rf "$temporary"' EXIT

mkdir -p "$temporary/$entry/document"
cp "$source_dir/ROOT" "$source_dir"/*.thy "$temporary/$entry/"
cp "$source_dir/document/root.tex" "$temporary/$entry/document/"
cp "$repository/LICENSE" "$temporary/$entry/"

tar -C "$temporary" -czf "$destination" "$entry"
printf '%s\n' "$destination"
