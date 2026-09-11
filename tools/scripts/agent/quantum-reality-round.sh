#!/usr/bin/env bash
# Dispatch one round of the standing quantum-reality research line to a browser
# oracle pool, and archive the reply in the lane. The charter and the carried
# open questions live in the lane so a round survives across sessions and hosts.
#
# Usage: quantum-reality-round.sh [lane-dir] [pool]
# Writes: <lane>/docs/reports/quantum-reality/round-<N>-<utc>.md
# Sentinel: QR_ROUND round=<N> status=dispatched|failed file=<path>
set -u

LANE="${1:-/Users/chronoai/trureturing-quantum-reality}"
POOL="${2:-chrono-chatgpt-pro-pool}"
DIR="$LANE/docs/reports/quantum-reality"
CHARTER="$DIR/CHARTER.md"
OPEN="$DIR/OPEN-QUESTIONS.md"

[ -f "$CHARTER" ] || { echo "QR_ROUND status=failed reason=no-charter path=$CHARTER"; exit 2; }
[ -f "$OPEN" ]    || { echo "QR_ROUND status=failed reason=no-open-questions path=$OPEN"; exit 2; }

mkdir -p "$DIR"
n=$(( $(find "$DIR" -maxdepth 1 -name 'round-*.md' | wc -l | tr -d ' ') + 5 ))
utc=$(date -u +%Y%m%dT%H%M%SZ)
head_sha=$(git -C "$LANE" rev-parse origin/dev 2>/dev/null || echo unknown)
brief=$(mktemp)
{
  printf '# 量子现实常设研究线 · 第 %s 轮\n\n' "$n"
  printf '本轮源码固定在 `%s`。取文件用\n' "$head_sha"
  printf '`https://github.com/the-omega-institute/trureturing/blob/%s/<path>`。\n\n' "$head_sha"
  cat "$CHARTER"
  printf '\n---\n\n'
  cat "$OPEN"
} > "$brief"

out="$DIR/round-$n-$utc.md"
if nyxid oracle ask "$POOL" --file "$brief" --tag "quantum-reality-r$n" > "$out" 2>&1; then
  echo "QR_ROUND round=$n status=dispatched file=$out pool=$POOL base=$head_sha"
  rm -f "$brief"; exit 0
fi
echo "QR_ROUND round=$n status=failed file=$out pool=$POOL"
rm -f "$brief"; exit 1
