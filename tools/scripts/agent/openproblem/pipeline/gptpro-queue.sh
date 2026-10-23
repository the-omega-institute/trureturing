#!/bin/bash
# Consume LANE ROLE ROUND PR lines and ask Nyx serially using prepared review briefs.
set -uo pipefail
. "$(dirname "$0")/common.sh"
[ "${1:-}" != --selftest ] || { op_selftest gptpro-queue; exit $?; }
[ "$#" -eq 0 ] || op_fail 10 USAGE gptpro-queue.sh
op_init; op_scratch
Q=${OP_GPTPRO_QUEUE:-$OP_SCRATCH/gptpro-queue.txt}
op_file "$Q"; op_file "$OP_REPO/tools/scripts/agent/nyx/nyx.py"
if [ -n "${OP_REVIEW_PREPARE:-}" ]; then
  op_file "$OP_REVIEW_PREPARE"
  [ -x "$OP_REVIEW_PREPARE" ] || op_fail 11 NOT_EXECUTABLE "$OP_REVIEW_PREPARE"
fi
# Keep the head line until its request completes; a failed request remains retryable.
op_lock "$OP_SCRATCH/gptpro-queue.lock" || op_fail 15 LOCK_TIMEOUT gptpro-queue.lock
trap 'rmdir "$OP_SCRATCH/gptpro-queue.lock"' EXIT
while :; do
  line=$(head -1 "$Q") || op_fail 16 IO_ERROR queue
  [ -n "$line" ] || { echo QUEUE_EMPTY; exit 0; }
  read -r lane role round pr extra <<< "$line"
  [ -n "$lane" ] && [ -n "$role" ] && [ -n "$round" ] && [ -n "$pr" ] && [ -z "$extra" ] || op_fail 13 INVALID_QUEUE_LINE "$line"
  op_name "$lane"; op_name "$role"; op_uint ROUND "$round"; op_uint PR "$pr"
  B=$OP_SCRATCH/briefs/review-$lane-$role.md
  O=$OP_SCRATCH/results/review-$lane-$role-r$round.out
  G=$OP_SCRATCH/logs/review-$lane-$role-r$round.log
  if [ -n "${OP_REVIEW_PREPARE:-}" ]; then
    "$OP_REVIEW_PREPARE" "$lane" "$role" "$round" "$pr" "$B" || op_fail 16 REVIEW_PREPARE_FAILED "$lane $role"
  fi
  op_file "$B"
  echo "QUEUE_RUN $line"
  op_gptpro_ask "$B" "$O" > "$G" 2>&1; rc=$?
  tail -1 "$G"
  echo "QUEUE_DONE $line rc=$rc"
  [ "$rc" -eq 0 ] || exit "$rc"
  tail -n +2 "$Q" > "$Q.tmp" && mv "$Q.tmp" "$Q" || op_fail 16 IO_ERROR queue
  echo NYX_SEAT_OK
done
