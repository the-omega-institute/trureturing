#!/bin/bash
# Return on an unseen terminal job log or after OP_WATCH_MAX_SECONDS.
set -uo pipefail
. "$(dirname "$0")/common.sh"
[ "${1:-}" != --selftest ] || { op_selftest watch-jobs; exit $?; }
[ "$#" -eq 0 ] || op_fail 10 USAGE watch-jobs.sh
op_init
limit=${OP_WATCH_MAX_SECONDS:-6600}; op_uint OP_WATCH_MAX_SECONDS "$limit"
mkdir -p "$OP_STATE/joblogs" || op_fail 16 IO_ERROR OP_STATE
touch "$OP_STATE/jobs-seen.txt" || op_fail 16 IO_ERROR jobs-seen.txt
SECONDS=0
while :; do
  found=0
  for f in "$OP_STATE/joblogs/"*.log; do
    [ -f "$f" ] || continue
    n=${f##*/}; n=${n%.log}
    last=$(tail -1 "$f") || op_fail 16 IO_ERROR "$f"
    [[ "$last" =~ ^JOB_EXIT=[0-9]+$ ]] || continue
    grep -Fxq -- "$n" "$OP_STATE/jobs-seen.txt"; seen=$?
    [ "$seen" -le 1 ] || op_fail 16 IO_ERROR jobs-seen.txt
    [ "$seen" -eq 1 ] || continue
    printf '== %s\n' "$n"; tail -8 "$f" | cut -c1-300
    printf '%s\n' "$n" >> "$OP_STATE/jobs-seen.txt" || op_fail 16 IO_ERROR jobs-seen.txt
    found=1
  done
  [ "$found" -eq 0 ] || exit 0
  [ "$SECONDS" -lt "$limit" ] || { echo WATCH_TIMEOUT; exit 0; }
  remaining=$((limit-SECONDS)); delay=$OP_POLL_SECONDS
  [ "$delay" -le "$remaining" ] || delay=$remaining
  sleep "$delay"
done
