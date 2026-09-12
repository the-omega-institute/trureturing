#!/usr/bin/env bash
# Stable shell entry point for Make, Actions, and tests. The canonical
# implementation lives in lean_cache_release.py; keep one transport path.
set -euo pipefail
exec python3 "$(dirname "${BASH_SOURCE[0]}")/lean_cache_release.py" "$@"
