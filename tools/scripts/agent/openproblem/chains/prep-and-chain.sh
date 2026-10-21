#!/bin/bash
# Usage: prep-and-chain.sh TYPE LANE WORKTREE A [B]
set -uo pipefail
command -v python3 >/dev/null 2>&1 || { printf 'CHAIN_TOOL_MISSING python3\n' >&2; exit 12; }
chain_dir=$(cd "$(dirname "$0")" && pwd -P)
python3 "$chain_dir/runtime.py" prep-and-chain "$@"
rc=$?
printf 'CHAIN_EXIT=%s\n' "$rc"
exit "$rc"
