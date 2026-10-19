#!/bin/bash
# Usage: seat-wait.sh NAME BRIEF WORKTREE STAGE [STAGGER].
set -uo pipefail
. "$(dirname "$0")/common.sh"
[ "${1:-}" != --selftest ] || { op_selftest seat-wait; exit $?; }
[ "$#" -ge 4 ] && [ "$#" -le 5 ] || op_fail 10 USAGE 'seat-wait.sh NAME BRIEF WORKTREE STAGE [STAGGER]'
op_init; op_scratch
NAME=$1; BRIEF=$2; WT=$3; STAGE=$4; STAG=${5:-0}
op_name "$NAME"; op_file "$BRIEF"
[ -d "$WT" ] || op_fail 11 INPUT_MISSING "$WT"
BRIEF=$(cd "$(dirname "$BRIEF")" && pwd -P)/$(basename "$BRIEF")
WT=$(cd "$WT" && pwd -P)
case "$STAGE" in thinking|implementation|review|termination) ;; *) op_fail 13 INVALID_STAGE "$STAGE";; esac
op_uint STAGGER "$STAG"
rounds=${OP_GATE_ROUNDS:-1440}; op_uint OP_GATE_ROUNDS "$rounds"
runner_delay=${OP_RUNNER_POLL_SECONDS:-5}; op_uint OP_RUNNER_POLL_SECONDS "$runner_delay"
since=${OP_WAIT_SINCE:-${DWF_WAIT_SINCE:-$(date +%s)}}; op_uint OP_WAIT_SINCE "$since"
locked=0; child=; registered=0
cleanup() {
  local cleanup_rc=0
  [ -z "$child" ] || wait "$child"
  [ "$locked" -eq 0 ] || rmdir "$OP_SCRATCH/gate.lock" || cleanup_rc=16
  if [ "$registered" -eq 1 ]; then
    rm -f "$OP_SCRATCH/waiters/$NAME.json" || cleanup_rc=16
    printf '%s \n' "$NAME" >> "$OP_SCRATCH/flights.txt" || cleanup_rc=16
  fi
  return "$cleanup_rc"
}
finish() {
  local status=$?
  trap - EXIT
  cleanup || { [ "$status" -ne 0 ] || status=16; }
  printf 'DISPATCH_EXIT=%s\n' "$status"
  exit "$status"
}
trap finish EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
if [ -f "$OP_SCRATCH/preset/$NAME" ]; then
  preset=$(op_data preset "$NAME") || exit $?
  PK=${preset%%$'\n'*}; PV=${preset#*$'\n'}
  if [ "$PK" = WAIT ]; then
    miss=0
    while [ "$miss" -lt 3 ]; do
      if op_snapshot; then
        if op_process alive "$PV"; then miss=0; else miss=$((miss+1)); fi
      else miss=0; fi
      [ "$miss" -ge 3 ] || sleep "$OP_POLL_SECONDS"
    done
    PV=$(op_latest_result "$PV") || exit $?
  fi
  rm "$OP_SCRATCH/preset/$NAME" || op_fail 16 IO_ERROR preset
  printf 'PRESET %s\n%s\n' "$NAME" "$PV"
  exit 0
fi
op_file "$OP_SCRATCH/briefs/process-safety-block.md"
op_file "$OP_REPO/tools/scripts/agent/seat/dispatch.sh"
# Resolve the SDK from PATH without depending on shell startup files.
if [ -z "${DOTNET_ROOT:-}" ] && command -v dotnet >/dev/null 2>&1; then
  DOTNET_ROOT=$(python3 -c 'import os,shutil;print(os.path.dirname(os.path.realpath(shutil.which("dotnet"))))'); export DOTNET_ROOT
fi
F=$(python3 -c 'import secrets;print(secrets.token_hex(12))') || op_fail 16 FLIGHT_ID generation
printf '%s %s\n' "$NAME" "$F" >> "$OP_SCRATCH/flights.txt" || op_fail 16 IO_ERROR flights.txt
op_data register "$NAME" "$F" "$WT" "$$" "$since" || exit $?
registered=1
cap_value() {
  cap=${OP_MAX_SEATS:-16}
  [ ! -f "$OP_SCRATCH/max-seats" ] || cap=$(cat "$OP_SCRATCH/max-seats") || op_fail 16 IO_ERROR max-seats
  op_uint max-seats "$cap"
  [ "$cap" -gt 0 ] || op_fail 13 INVALID_INPUT 'max-seats must be positive'
}
pass_gate() {
  local g=0 why=unavailable
  while [ "$g" -lt "$rounds" ]; do
    op_lock "$OP_SCRATCH/gate.lock" || op_fail 15 LOCK_TIMEOUT gate.lock
    locked=1
    cap_value
    op_snapshot || op_fail 16 PROCESS_LIST_FAILED ps
    if why=$(op_process gate "$NAME" "$WT" "$cap" "$since"); then
      echo "LOCKED_GATE_PASS $why cap=$cap"; return 0
    else
      rc=$?; [ "$rc" -eq 1 ] || exit "$rc"
    fi
    rmdir "$OP_SCRATCH/gate.lock" || op_fail 16 IO_ERROR gate.lock
    locked=0; echo "GATE_WAIT $why cap=$cap"
    g=$((g+1)); sleep "$OP_POLL_SECONDS"
  done
  op_fail 15 GATE_TIMEOUT "$why"
}
BRIEF2=$OP_SCRATCH/briefs/.dispatched-$F.md
{ cat "$BRIEF"; printf '\n'; sed "s/__FLIGHT__/$F/g" "$OP_SCRATCH/briefs/process-safety-block.md"; } > "$BRIEF2" || op_fail 16 IO_ERROR brief
rc=16
for attempt in 1 2 3 4 5 6; do
  pass_gate
  if [ "$STAGE" != thinking ]; then
    bash "$OP_PIPELINE_DIR/refresh-if-stale.sh" "$WT" || exit $?
  fi
  # Dispatch remains the sole runner launcher. This parent joins its child.
  dispatch_log=$OP_SCRATCH/logs/dispatch-$F.log
  (cd "$OP_REPO" && bash tools/scripts/agent/seat/dispatch.sh "$F" 1 "$BRIEF2" "$WT" "$STAGE" "$STAG" "$cap") > "$dispatch_log" 2>&1 &
  child=$!
  child_running() { case " $(jobs -rp | tr '\n' ' ') " in *" $child "*) return 0;; *) return 1;; esac; }
  while child_running; do
    if op_snapshot && op_process alive "$F"; then break; fi
    sleep "$runner_delay"
  done
  # A started runner reserves the seat; otherwise keep the lock until dispatch returns.
  if child_running; then
    rmdir "$OP_SCRATCH/gate.lock" || op_fail 16 IO_ERROR gate.lock
    locked=0
  fi
  wait "$child"; rc=$?; child=
  cat "$dispatch_log"
  terminal=$(tail -1 "$dispatch_log")
  if [ "$rc" -eq 0 ] && [[ "$terminal" =~ ^RUNNER_EXIT=([0-9]+)$ ]]; then rc=${BASH_REMATCH[1]}; fi
  if [ "$locked" -eq 1 ]; then rmdir "$OP_SCRATCH/gate.lock"; locked=0; fi
  [ "$rc" -eq 4 ] || break
  echo "REQUEUE after gate timeout ($attempt)"
done
# Reap only the finished flight's Lean/Lake/Python executables, never a carrier shell.
if op_snapshot && ! op_process alive "$F"; then
  for p in $(op_process reap "$F"); do
    c=$(ps -o comm= -p "$p") || continue
    case "${c##*/}" in lean|lake|python|python3|Python) echo "REAP pid=$p comm=${c##*/}"; kill "$p" 2>/dev/null;; esac
  done
fi
exit "$rc"
