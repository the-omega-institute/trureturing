#!/bin/bash
# Usage: JOB=NAME CMD=COMMAND migrate-chain.sh [--dry-run] PROCESS_PATTERN STEP...
# Preserve runner subtrees; signal only the uniquely identified chain shell.
set -uo pipefail
. "$(dirname "$0")/common.sh"
[ "${1:-}" != --selftest ] || { op_selftest migrate-chain; exit $?; }
dry=0
[ "${1:-}" != --dry-run ] || { dry=1; shift; }
[ "$#" -ge 2 ] || op_fail 10 USAGE 'migrate-chain.sh [--dry-run] PROCESS_PATTERN STEP...'
op_init; op_scratch
[ -n "${JOB:-}" ] && [ -n "${CMD:-}" ] || op_fail 11 INPUT_MISSING 'JOB and CMD'
op_name "$JOB"
pattern=$1; shift
op_snapshot || op_fail 16 PROCESS_LIST_FAILED ps
chain=$(op_process migration "$pattern" "$$") || exit $?
[ ! -e "$OP_STATE/spool/$JOB.job" ] || op_fail 14 JOB_EXISTS "$JOB"
op_presets "$dry" "$@"
if [ "$dry" -eq 0 ]; then
  # A fresh reading must identify the same shell immediately before signalling.
  op_snapshot || op_fail 16 PROCESS_LIST_FAILED ps
  current=$(op_process migration "$pattern" "$$") || exit $?
  [ "$current" = "$chain" ] || op_fail 14 PROCESS_CHANGED "$chain"
  kill -TERM "$chain" || op_fail 16 MIGRATE_SIGNAL_FAILED "$chain"
  op_spool "$JOB" "$CMD"
fi
echo "MIGRATED $JOB chain=$chain dry_run=$dry"
