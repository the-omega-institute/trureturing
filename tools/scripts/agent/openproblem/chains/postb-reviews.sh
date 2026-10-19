#!/bin/bash
# Usage: postb-reviews.sh LANE PR WORKTREE
set -uo pipefail
command -v python3 >/dev/null 2>&1 || { printf 'CHAIN_TOOL_MISSING python3\n' >&2; exit 12; }
chain_dir=$(cd "$(dirname "$0")" && pwd -P)
if [ "${1:-}" = --selftest ]; then
  exec python3 "$chain_dir/selftest.py" postb-reviews
fi
python3 "$chain_dir/runtime.py" postb-prepare "$@" || exit $?
pids=()
for role in architecture quality tests; do
  python3 "$chain_dir/runtime.py" review-one "$1" "$role" "$3" &
  pids[${#pids[@]}]=$!
done
rc=0
for pid in "${pids[@]}"; do
  wait "$pid" || rc=$?
done
printf 'CHAIN_EXIT=%s\n' "$rc"
exit "$rc"
