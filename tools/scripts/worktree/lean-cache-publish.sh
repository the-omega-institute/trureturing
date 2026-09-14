#!/usr/bin/env bash
# Release snapshots are optional seeds. The caller owns the private cache writer.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
exec python3 "$SCRIPT_DIR/lean_cache_release.py" "$@"
