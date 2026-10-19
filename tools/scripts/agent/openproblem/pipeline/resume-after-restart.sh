#!/bin/bash
# Re-spool unfinished jobs and restore available step presets. Usage: [--dry-run].
set -uo pipefail
. "$(dirname "$0")/common.sh"
[ "${1:-}" != --selftest ] || { op_selftest resume-after-restart; exit $?; }
dry=0
case "$#:${1:-}" in 0:) ;; 1:--dry-run) dry=1;; *) op_fail 10 USAGE 'resume-after-restart.sh [--dry-run]';; esac
op_init; op_scratch
mkdir -p "$OP_STATE/spool" "$OP_STATE/joblogs" || op_fail 16 IO_ERROR OP_STATE
for job in "$OP_STATE/running/"*.job; do
  [ -f "$job" ] || continue
  n=${job##*/}; n=${n%.job}; op_name "$n"
  log=$OP_STATE/joblogs/$n.log
  if [ -f "$log" ] && grep -Eq '^JOB_EXIT=[0-9]+$' "$log"; then
    if [ ! -f "$OP_STATE/respool-after-recovery.txt" ] || ! grep -Fxq -- "$n" "$OP_STATE/respool-after-recovery.txt"; then continue; fi
  fi
  echo "resume $n"
  # Chain steps are layer-2 data, one unprefixed STEP per line in running/NAME.steps.
  steps=$OP_STATE/running/$n.steps
  set --
  if [ -f "$steps" ]; then
    while IFS= read -r step || [ -n "$step" ]; do [ -z "$step" ] || set -- "$@" "$step"; done < "$steps"
  else
    derived=$(op_data steps "$job") || exit $?
    while IFS= read -r step; do [ -z "$step" ] || set -- "$@" "$step"; done <<< "$derived"
  fi
  [ "$#" -eq 0 ] || op_presets "$dry" "$@"
  if [ "$dry" -eq 0 ]; then
    command=$(cat "$job") || op_fail 16 IO_ERROR "$job"
    op_spool "$n" "$command"
    [ ! -f "$log" ] || mv "$log" "$OP_STATE/joblogs/$n.pre-restart.log" || op_fail 16 IO_ERROR log
    rm "$job" || op_fail 16 IO_ERROR "$job"
  fi
done
echo RESUME_DONE
