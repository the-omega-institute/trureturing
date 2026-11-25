#!/usr/bin/env bash
set -euo pipefail

# The dependency cache may contain mathlib sources with only a subset of their oleans.
receipt="$RUNNER_TEMP/lean-compile-dependencies.log"
make lean-cache-ensure FULL_BUILD=1 | tee "$receipt"
if sed -n 's/^LEAN_CACHE //p' "$receipt" | jq -se 'any(.[]; .mathlib_missing_olean_files == 0 and .mathlib_olean_state == "warm")' >/dev/null; then
  exit 0
fi
bash tools/scripts/worktree/lean-cache-run.sh lake exe cache get
