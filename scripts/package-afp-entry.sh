#!/usr/bin/env bash
set -euo pipefail

repository=$(cd "$(dirname "$0")/.." && pwd)
exec python3 "$repository/scripts/package_afp_entry.py" "$@"
