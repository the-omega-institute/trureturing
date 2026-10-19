#!/bin/bash
# Usage: stagea.sh LANE WORKTREE CONTINUATION MIRROR (CONTINUATION=- starts at mirror)
set -uo pipefail
command -v python3 >/dev/null 2>&1 || { printf 'CHAIN_TOOL_MISSING python3\n' >&2; exit 12; }
chain_dir=$(cd "$(dirname "$0")" && pwd -P)
python3 "$chain_dir/runtime.py" stagea "$@"
rc=$?
printf 'CHAIN_EXIT=%s\n' "$rc"
exit "$rc"
