#!/bin/bash
set -uo pipefail
command -v python3 >/dev/null 2>&1 || { printf "PIPELINE_TOOL_MISSING python3\n" >&2; exit 12; }
entry_dir=$(cd "$(dirname "$0")" && pwd -P)
exec python3 "$entry_dir/landing.py" land-watch "$@"
