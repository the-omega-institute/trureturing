#!/usr/bin/env bash
set -euo pipefail

export LC_ALL=C

ROLE=""
LEAN_SLOT=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    --role)
      [[ $# -ge 2 ]] || { echo "report-supervisor: --role requires a value" >&2; exit 2; }
      ROLE="$2"
      shift 2
      ;;
    --lean-slot) LEAN_SLOT=1; shift ;;
    --) shift; break ;;
    *) echo "report-supervisor: unknown argument '$1'" >&2; exit 2 ;;
  esac
done

[[ "$ROLE" =~ ^[a-z0-9][a-z0-9-]*$ ]] \
  || { echo "report-supervisor: --role must use lowercase ASCII words" >&2; exit 2; }
[[ $# -gt 0 ]] || { echo "report-supervisor: command is required after --" >&2; exit 2; }

if [[ -d /private/tmp ]]; then DEFAULT_HOST_TMP=/private/tmp; else DEFAULT_HOST_TMP=/tmp; fi
STATE_ROOT="${STRATALINT_SUPERVISOR_ROOT:-$DEFAULT_HOST_TMP/stratalint-report-supervisor-${UID:-$(id -u)}}"
RUN_ROOT="$STATE_ROOT/runs"
SLOT_ROOT="$STATE_ROOT/slots"
METRICS_LOG="${STRATALINT_REPORT_METRICS_LOG:-$STATE_ROOT/measurements.jsonl}"
MAX_CONCURRENCY="${STRATALINT_LEAN_MAX_CONCURRENCY:-1}"
[[ "$MAX_CONCURRENCY" =~ ^[1-9][0-9]*$ && "$MAX_CONCURRENCY" -le 64 ]] \
  || { echo "report-supervisor: STRATALINT_LEAN_MAX_CONCURRENCY must be 1..64" >&2; exit 2; }

mkdir -p "$RUN_ROOT" "$SLOT_ROOT" "$(dirname "$METRICS_LOG")"
TMP_ROOT="$(mktemp -d "$RUN_ROOT/run.XXXXXXXX")"
SCRATCH="$TMP_ROOT/scratch"
mkdir -p "$SCRATCH"

CHILD_PID=""
PROCESS_GROUP_ID=""
SLOT_DIR=""
CONCURRENCY_COUNT=0
FD_PEAK=0
RSS_PEAK_KB=0
STARTED_MS=0

now_ms() {
  if command -v perl >/dev/null 2>&1; then
    perl -MTime::HiRes=time -e 'printf "%.0f\n", time() * 1000'
  else
    printf '%s000\n' "$(date +%s)"
  fi
}

process_exists() { kill -0 "$1" >/dev/null 2>&1; }

reclaim_stale_lock() {
  local lock="$1"
  local owner=""
  [[ -f "$lock/owner" ]] || return 1
  read -r owner < "$lock/owner" || return 1
  [[ "$owner" =~ ^[1-9][0-9]*$ ]] || return 1
  if process_exists "$owner"; then return 1; fi
  local stale="${lock}.stale.$$.$RANDOM"
  if mv "$lock" "$stale" 2>/dev/null; then
    rm -rf -- "$stale"
    return 0
  fi
  return 1
}

active_slot_count() {
  find "$SLOT_ROOT" -maxdepth 1 -type d -name 'slot-*.lock' -print 2>/dev/null \
    | awk 'END {print NR + 0}'
}

acquire_lean_slot() {
  local index
  local candidate
  while true; do
    for ((index = 1; index <= MAX_CONCURRENCY; index++)); do
      candidate="$SLOT_ROOT/slot-$index.lock"
      if mkdir "$candidate" 2>/dev/null; then
        printf '%s\n' "$$" > "$candidate/owner"
        SLOT_DIR="$candidate"
        CONCURRENCY_COUNT="$(active_slot_count)"
        return 0
      fi
      reclaim_stale_lock "$candidate" || true
    done
    sleep 0.1
  done
}

collect_process_tree() {
  local queue=("$1")
  local index=0
  local pid
  local child
  while [[ "$index" -lt "${#queue[@]}" ]]; do
    pid="${queue[$index]}"
    index=$((index + 1))
    printf '%s\n' "$pid"
    while IFS= read -r child; do
      [[ -n "$child" ]] && queue+=("$child")
    done < <(pgrep -P "$pid" 2>/dev/null || true)
  done
}

sample_process_tree() {
  local pid rss fd
  local rss_total=0
  local fd_total=0
  while IFS= read -r pid; do
    [[ -n "$pid" ]] || continue
    rss="$( { ps -o rss= -p "$pid" 2>/dev/null || true; } | awk '{sum += $1} END {print sum + 0}')"
    rss_total=$((rss_total + rss))
    if [[ -d "/proc/$pid/fd" ]]; then
      fd="$( { find "/proc/$pid/fd" -mindepth 1 -maxdepth 1 -print 2>/dev/null || true; } | awk 'END {print NR + 0}')"
    elif command -v lsof >/dev/null 2>&1; then
      fd="$( { lsof -a -p "$pid" -d 0-999999 2>/dev/null || true; } | awk 'NR > 1 {count++} END {print count + 0}')"
    else
      fd=0
    fi
    fd_total=$((fd_total + fd))
  done < <(collect_process_tree "$CHILD_PID")
  if [[ "$rss_total" -gt "$RSS_PEAK_KB" ]]; then RSS_PEAK_KB="$rss_total"; fi
  if [[ "$fd_total" -gt "$FD_PEAK" ]]; then FD_PEAK="$fd_total"; fi
}

terminate_process_group() {
  local group_id="$1"
  kill -TERM -- "-$group_id" >/dev/null 2>&1 || true
  sleep 0.2
  kill -KILL -- "-$group_id" >/dev/null 2>&1 || true
}

append_metrics() {
  local rc="$1"
  local elapsed_ms="$2"
  local metrics_lock="${METRICS_LOG}.lock"
  while ! mkdir "$metrics_lock" 2>/dev/null; do
    reclaim_stale_lock "$metrics_lock" || true
    sleep 0.05
  done
  printf '%s\n' "$$" > "$metrics_lock/owner"
  printf '{"ts":"%s","role":"%s","pid":%s,"elapsed_ms":%s,"rc":%s,"fd_peak":%s,"rss_peak_kb":%s,"concurrency_count":%s}\n' \
    "$(date -u '+%Y-%m-%dT%H:%M:%SZ')" "$ROLE" "$CHILD_PID" "$elapsed_ms" "$rc" \
    "$FD_PEAK" "$RSS_PEAK_KB" "$CONCURRENCY_COUNT" >> "$METRICS_LOG"
  rm -rf -- "$metrics_lock"
}

finish() {
  local rc=$?
  local finished_ms
  trap - EXIT HUP INT TERM
  set +e
  if [[ -n "$PROCESS_GROUP_ID" ]]; then
    terminate_process_group "$PROCESS_GROUP_ID"
  fi
  if [[ -n "$CHILD_PID" ]]; then
    wait "$CHILD_PID" >/dev/null 2>&1 || true
  fi
  finished_ms="$(now_ms)"
  if [[ -n "$CHILD_PID" && "$STARTED_MS" -gt 0 ]]; then
    append_metrics "$rc" "$((finished_ms - STARTED_MS))"
  fi
  if [[ -n "$SLOT_DIR" ]]; then rm -rf -- "$SLOT_DIR"; fi
  rm -rf -- "$TMP_ROOT"
  exit "$rc"
}

trap finish EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

if [[ "$LEAN_SLOT" == "1" ]]; then
  acquire_lean_slot
else
  CONCURRENCY_COUNT="$(active_slot_count)"
fi

STARTED_MS="$(now_ms)"
set -m
TMPDIR="$SCRATCH" "$@" &
CHILD_PID=$!
PROCESS_GROUP_ID="$CHILD_PID"
set +m
while process_exists "$CHILD_PID"; do
  sample_process_tree
  sleep 0.1
done
set +e
wait "$CHILD_PID"
rc=$?
set -e
exit "$rc"
