#!/bin/bash
# Print module names touched by in-flight math branches.
set -euo pipefail
REPO="${1:?usage: inflight_mods.sh REPO [OUT_MODS]}"
OUT_M="${2:-/dev/stdout}"
cd "$REPO"
while read -r branch; do
  git diff --name-only "origin/dev...$branch" -- D5
done < <(git for-each-ref --format='%(refname:short)' 'refs/remotes/origin/lane/math/*') \
  | sed -n 's|.*/||;s|\.lean$||p' | sort -u > "$OUT_M"
