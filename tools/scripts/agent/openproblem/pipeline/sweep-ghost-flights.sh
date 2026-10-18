#!/bin/bash
# Tombstone recorded flights whose directory exists and whose runner is absent.
set -uo pipefail
. "$(dirname "$0")/common.sh"
[ "${1:-}" != --selftest ] || { op_selftest sweep-ghost-flights; exit $?; }
[ "$#" -eq 0 ] || op_fail 10 USAGE sweep-ghost-flights.sh
op_init; op_scratch
op_snapshot || op_fail 16 PROCESS_LIST_FAILED ps
finished=$(op_process sweep) || exit $?
while read -r name flight; do
  [ -n "$name" ] || continue
  printf '%s \n' "$name" >> "$OP_SCRATCH/flights.txt" || op_fail 16 IO_ERROR flights.txt
  echo "TOMBSTONE $name $flight"
done <<< "$finished"
