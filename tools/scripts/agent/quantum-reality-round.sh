#!/usr/bin/env bash
# Dispatch one round of the standing quantum-reality research line to a browser
# oracle pool, and archive the reply in the lane. The charter and the carried
# open questions live in the lane so a round survives across sessions and hosts.
#
#
# It dispatches through the repository's own nyxid client, `nyx.sh`, and not
# through `nyxid oracle ask` directly. The direct call was the line's single
# largest carrier problem and it took three rounds to see, because everything
# `nyx.sh` had been hardened to do was simply bypassed:
#
#   * **the mode tag was wrong.** This script passed `--tag quantum-reality-r<N>`
#     as its only tag, so no `mode:chat` ever reached the pool;
#     `company-chatgpt-pro` answered `oracle_mode_required` and the line recorded
#     that pool as "structurally unusable through this runner". It is not --
#     `nyx.sh` sets `mode:chat` by default and the same pool accepts submissions
#     under it. The round is still identified: its number is in the filename.
#   * **no pool traversal.** A fixed pool meant one carrier failure ended a round.
#   * **no verdict classification.** `nyxid oracle ask` exits nonzero for a dozen
#     unrelated reasons; the caller saw only `status=failed` and had to read the
#     `Error:` line out of the archive by hand to tell "carrier broke, try the
#     next pool" from "session expired, a human must log in".
#   * **no task-id sidecar.** A timeout leaves a task still running upstream.
#     Without the sidecar the only move left was to redispatch, which is exactly
#     what must not be done.
#
# Usage: quantum-reality-round.sh [lane-dir] [pool]
# `pool` is optional and normally omitted: empty lets `nyx.sh` rank the usable
# pools and traverse them. Pass one only to pin a specific carrier.
# Writes: <lane>/docs/reports/quantum-reality/round-<N>-<utc>.md
# Sentinel: QR_ROUND round=<N> status=dispatched|failed file=<path>
set -u

LANE="${1:-/Users/chronoai/trureturing-quantum-reality}"
POOL="${2:-}"
NYX="$(dirname "$0")/nyx.sh"
[ -f "$NYX" ] || { echo "QR_ROUND status=failed reason=no-nyx path=$NYX"; exit 2; }
DIR="$LANE/docs/reports/quantum-reality"
CHARTER="$DIR/CHARTER.md"
OPEN="$DIR/OPEN-QUESTIONS.md"

[ -f "$CHARTER" ] || { echo "QR_ROUND status=failed reason=no-charter path=$CHARTER"; exit 2; }
[ -f "$OPEN" ]    || { echo "QR_ROUND status=failed reason=no-open-questions path=$OPEN"; exit 2; }

mkdir -p "$DIR"
# The round number comes from the carried open-questions text, not from the
# archive files.
#
# Two earlier derivations were wrong, each for its own reason, and the second is
# the one that matters:
#
#   count(round-*.md) + 5   undershoots by exactly the number of failed rounds,
#                           because a failed round's archive is deleted on
#                           purpose. It produced 10, 11, 12, 13 while the real
#                           rounds were 12, 14, 15, 16.
#
#   max(round-*.md) + 1     fixes the counting error and is still wrong, because
#                           **the archives are never committed**. They are
#                           run-local outputs of whichever worktree ran the
#                           round, and they vanish the moment that lane is reset
#                           to the dev tip. Measured 2026-09-11: dev carries
#                           archives 5,6,7,8,10,12,14,15 while OPEN-QUESTIONS.md
#                           — which is committed — already names rounds 10
#                           through 18. A freshly synced lane therefore dispatched
#                           round 19 under the filename round-16.
#
# OPEN-QUESTIONS.md is the line's carried state: the dispatcher already refuses
# to run without it, it is committed, and every round writes its own heading
# into it. So the round number is the largest `第 N 轮` it mentions, plus one.
# Fail closed if the file names no round at all, rather than silently restarting
# at 1 and overwriting history.
n=$(grep -oE '第 [0-9]+ 轮' "$OPEN" 2>/dev/null | grep -oE '[0-9]+' | sort -n | tail -1)
case "$n" in
  ''|*[!0-9]*) echo "QR_ROUND status=failed reason=no-round-number-in-open-questions path=$OPEN"; exit 2 ;;
esac
n=$(( n + 1 ))
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
if NYX_POOL="$POOL" bash "$NYX" ask "$brief" "$out"; then
  echo "QR_ROUND round=$n status=dispatched file=$out pool=${POOL:-traversed} base=$head_sha"
  rm -f "$brief"; exit 0
fi
rc=$?
# nyx.sh has already printed a classified NYX_* line and, on a timeout, written
# the task id to "$out.taskid". Carry its exit code through instead of flattening
# every failure to 1: the caller's next move differs by verdict.
echo "QR_ROUND round=$n status=failed file=$out pool=${POOL:-traversed} nyx_rc=$rc"
rm -f "$brief"; exit "$rc"
