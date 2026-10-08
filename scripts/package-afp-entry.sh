#!/usr/bin/env bash
set -euo pipefail

repository=$(cd "$(dirname "$0")/.." && pwd)
entry=Set_Coded_Computation_ZF
source_dir="$repository/Turing_Machines_ZF/Core"
destination=${1:-"$repository/$entry.tar.gz"}
temporary=$(mktemp -d)
trap 'rm -rf "$temporary"' EXIT

mkdir -p "$temporary/$entry/document"
cp "$source_dir/ROOT" "$source_dir"/*.thy "$temporary/$entry/"
cp "$source_dir/document/root.tex" "$temporary/$entry/document/"
cp "$repository/LICENSE" "$temporary/$entry/"

tar -C "$temporary" -czf "$destination" "$entry"
printf '%s\n' "$destination"
