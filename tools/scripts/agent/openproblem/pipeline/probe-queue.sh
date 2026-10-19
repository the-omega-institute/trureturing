#!/bin/bash
# Usage: probe-queue.sh [KEY...]. OP_LANES contains KEY:SUFFIX entries.
set -uo pipefail
. "$(dirname "$0")/common.sh"
[ "${1:-}" != --selftest ] || { op_selftest probe-queue; exit $?; }
op_init; op_scratch; op_main; op_need make
[ -n "${OP_PENDING:-}" ] || op_fail 11 INPUT_MISSING OP_PENDING
[ -d "$OP_PENDING" ] || op_fail 11 INPUT_MISSING "$OP_PENDING"
[ -n "${OP_LANES:-}" ] || op_fail 11 INPUT_MISSING OP_LANES
[ -n "${OP_WORKTREE_PATTERN:-}" ] || op_fail 11 INPUT_MISSING OP_WORKTREE_PATTERN
case "$OP_WORKTREE_PATTERN" in *'{suffix}'*) ;; *) op_fail 13 INVALID_INPUT 'OP_WORKTREE_PATTERN requires {suffix}';; esac
K=${PQ_WAITERS:-16}; op_uint PQ_WAITERS "$K"
[ "$K" -gt 0 ] || op_fail 13 INVALID_INPUT 'PQ_WAITERS must be positive'
children=
cleanup() { local p; for p in $children; do wait "$p"; done; return 0; }
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
# Validate every mapping before creating any worktree.
for lane in $OP_LANES; do
  case "$lane" in *:*) ;; *) op_fail 13 INVALID_INPUT "lane $lane requires KEY:SUFFIX";; esac
  op_name "${lane%%:*}"; op_name "${lane#*:}"
done
ordered=
for key in ${PQ_FIRST:-}; do
  for lane in $OP_LANES; do [ "${lane%%:*}" != "$key" ] || ordered="$ordered $lane"; done
done
for lane in $OP_LANES; do
  case " ${PQ_FIRST:-} " in *" ${lane%%:*} "*) ;; *) ordered="$ordered $lane";; esac
done
for lane in $ordered; do
  key=${lane%%:*}; suffix=${lane#*:}
  [ "$suffix" != - ] || continue
  if [ "$#" -gt 0 ]; then
    selected=0
    for arg in "$@"; do [ "$arg" != "$key" ] || selected=1; done
    [ "$selected" -eq 1 ] || continue
  fi
  brief=$OP_SCRATCH/briefs/probe-$key-r1.md
  [ -f "$brief" ] || { echo "no brief $key"; continue; }
  if [ -f "$OP_SCRATCH/pq-dispatched.txt" ] && grep -Fxq -- "$key" "$OP_SCRATCH/pq-dispatched.txt"; then echo "already dispatched $key"; continue; fi
  tree=${OP_WORKTREE_PATTERN//\{suffix\}/$suffix}
  case "$tree" in /*) ;; *) tree=$OP_MAIN/$tree;; esac
  if [ ! -d "$tree" ]; then
    (cd "$OP_MAIN" && make worktree KIND=math NAME="op-$key" DEST="$tree") >> "$OP_SCRATCH/logs/pq-worktree-$key.log" 2>&1 || op_fail 16 WORKTREE_FAILED "$key"
  fi
  [ -d "$tree" ] || op_fail 11 INPUT_MISSING "$tree"
  op_snapshot || op_fail 16 PROCESS_LIST_FAILED ps
  if op_process busy "$tree"; then
    echo "PREP_SKIP worktree-busy $tree"
  else
    make -C "$tree" lean-cache-ensure >> "$OP_SCRATCH/logs/pq-ensure-$key.log" 2>&1 || op_fail 16 CACHE_ENSURE_FAILED "$key"
  fi
  while [ "$(jobs -rp | wc -l | tr -d ' ')" -ge "$K" ]; do sleep "$OP_POLL_SECONDS"; done
  bash "$OP_PIPELINE_DIR/seat-wait.sh" "${OP_NAME_PREFIX}probe-$key-r1" "$brief" "$tree" thinking 0 > "$OP_SCRATCH/logs/probe-$key-r1.log" 2>&1 &
  children="$children $!"
  printf '%s\n' "$key" >> "$OP_SCRATCH/pq-dispatched.txt" || op_fail 16 IO_ERROR pq-dispatched.txt
  echo "queued $key"
done
rc=0
for p in $children; do wait "$p" || rc=1; done
children=
echo "PROBE_QUEUE=$rc"
exit "$rc"
