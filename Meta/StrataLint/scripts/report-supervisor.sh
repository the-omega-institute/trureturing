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

REPOSITORY_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
if [[ -d /private/tmp ]]; then DEFAULT_HOST_TMP=/private/tmp; else DEFAULT_HOST_TMP=/tmp; fi
STATE_ROOT="${STRATALINT_SUPERVISOR_ROOT:-$DEFAULT_HOST_TMP/stratalint-report-supervisor-${UID:-$(id -u)}}"
RUN_ROOT="$STATE_ROOT/runs"
SLOT_ROOT="$STATE_ROOT/slots"
if [[ -n "${STRATALINT_REPORT_METRICS_LOG:-}" ]]; then
  METRICS_LOG="$STRATALINT_REPORT_METRICS_LOG"
else
  [[ -n "${HOME:-}" && "$HOME" == /* ]] \
    || { echo "report-supervisor: HOME must be absolute for the performance ledger" >&2; exit 2; }
  METRICS_LOG="$HOME/.stratalint-perf/events.jsonl"
fi
MAX_CONCURRENCY="${STRATALINT_LEAN_MAX_CONCURRENCY:-1}"
[[ "$MAX_CONCURRENCY" =~ ^[1-9][0-9]*$ && "$MAX_CONCURRENCY" -le 64 ]] \
  || { echo "report-supervisor: STRATALINT_LEAN_MAX_CONCURRENCY must be 1..64" >&2; exit 2; }
LOCK_TIMEOUT_SECONDS="${STRATALINT_LOCK_TIMEOUT_SECONDS:-900}"
[[ "$LOCK_TIMEOUT_SECONDS" =~ ^[1-9][0-9]*$ && "$LOCK_TIMEOUT_SECONDS" -le 86400 ]] \
  || { echo "report-supervisor: STRATALINT_LOCK_TIMEOUT_SECONDS must be 1..86400" >&2; exit 2; }
LOCK_STALE_SECONDS="${STRATALINT_LOCK_STALE_SECONDS:-5}"
[[ "$LOCK_STALE_SECONDS" =~ ^[0-9]+$ && "$LOCK_STALE_SECONDS" -le 60 ]] \
  || { echo "report-supervisor: STRATALINT_LOCK_STALE_SECONDS must be 0..60" >&2; exit 2; }

mkdir -p "$RUN_ROOT" "$SLOT_ROOT" "$(dirname "$METRICS_LOG")"
TMP_ROOT="$(mktemp -d "$RUN_ROOT/run.XXXXXXXX")"
SCRATCH="$TMP_ROOT/scratch"
mkdir -p "$SCRATCH"
DESCENDANT_PIDS="$TMP_ROOT/descendant-pids"
: > "$DESCENDANT_PIDS"

CHILD_PID=""
PROCESS_GROUP_ID=""
SLOT_DIR=""
METRICS_LOCK_DIR=""
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

lock_mtime() {
  if stat -f '%m' "$1" >/dev/null 2>&1; then
    stat -f '%m' "$1"
  else
    stat -c '%Y' "$1" 2>/dev/null
  fi
}

reclaim_stale_lock() {
  local lock="$1"
  local owner=""
  local mtime=""
  if [[ -f "$lock/owner" ]]; then
    read -r owner < "$lock/owner" || owner=""
  fi
  if [[ "$owner" =~ ^[1-9][0-9]*$ ]]; then
    if process_exists "$owner"; then return 1; fi
  else
    mtime="$(lock_mtime "$lock" || true)"
    [[ "$mtime" =~ ^[0-9]+$ ]] || return 1
    if (( $(date +%s) - mtime < LOCK_STALE_SECONDS )); then return 1; fi
  fi
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
  local deadline=$(( $(date +%s) + LOCK_TIMEOUT_SECONDS ))
  while true; do
    for ((index = 1; index <= MAX_CONCURRENCY; index++)); do
      candidate="$SLOT_ROOT/slot-$index.lock"
      if mkdir "$candidate" 2>/dev/null; then
        SLOT_DIR="$candidate"
        printf '%s\n' "$$" > "$candidate/owner" \
          || { echo "report-supervisor: could not record Lean slot owner" >&2; return 2; }
        CONCURRENCY_COUNT="$(active_slot_count)"
        return 0
      fi
      reclaim_stale_lock "$candidate" || true
    done
    if (( $(date +%s) >= deadline )); then
      echo "report-supervisor: timed out waiting for a Lean slot" >&2
      return 2
    fi
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
    printf '%s\n' "$pid" >> "$DESCENDANT_PIDS"
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

signal_recorded_tree() {
  local signal="$1"
  local pid
  sort -run "$DESCENDANT_PIDS" 2>/dev/null | while IFS= read -r pid; do
    [[ "$pid" =~ ^[1-9][0-9]*$ && "$pid" != "$$" ]] || continue
    kill "-$signal" "$pid" >/dev/null 2>&1 || true
  done
}

terminate_process_group() {
  local group_id="$1"
  signal_recorded_tree TERM
  kill -TERM -- "-$group_id" >/dev/null 2>&1 || true
  sleep 0.2
  signal_recorded_tree KILL
  kill -KILL -- "-$group_id" >/dev/null 2>&1 || true
}

loadavg_per_cpu() {
  local load=""
  local cpus=""
  if [[ -r /proc/loadavg ]]; then
    read -r load _ < /proc/loadavg || true
  elif command -v sysctl >/dev/null 2>&1; then
    load="$(sysctl -n vm.loadavg 2>/dev/null \
      | awk '{for (i=1; i<=NF; i++) if ($i ~ /^[0-9]+([.][0-9]+)?$/) {print $i; exit}}')"
  fi
  if command -v getconf >/dev/null 2>&1; then
    cpus="$(getconf _NPROCESSORS_ONLN 2>/dev/null || true)"
  fi
  if [[ ! "$cpus" =~ ^[1-9][0-9]*$ ]] && command -v sysctl >/dev/null 2>&1; then
    cpus="$(sysctl -n hw.logicalcpu 2>/dev/null || true)"
  fi
  if [[ "$load" =~ ^[0-9]+([.][0-9]+)?$ && "$cpus" =~ ^[1-9][0-9]*$ ]]; then
    awk -v load="$load" -v cpus="$cpus" 'BEGIN {printf "%.6f", load / cpus}'
  else
    printf 'null'
  fi
}

performance_event() {
  local rc="$1"
  local elapsed_ms="$2"
  local timestamp status venue os arch commit base load elapsed_seconds rss_peak_mb
  timestamp="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  status=passed
  if [[ "$rc" -ne 0 ]]; then status=failed; fi
  venue=local
  if [[ "${CI:-}" == "true" || "${CI:-}" == "1" ]]; then venue=ci; fi
  os="$(uname -s 2>/dev/null || printf unknown)"
  arch="$(uname -m 2>/dev/null || printf unknown)"
  commit="$(git -C "$REPOSITORY_ROOT" rev-parse --verify 'HEAD^{commit}' 2>/dev/null || printf unknown)"
  [[ "$commit" =~ ^[0-9a-f]{40,64}$ ]] || commit=unknown
  base="$(git -C "$REPOSITORY_ROOT" rev-parse --verify "${STRATALINT_PERF_BASE:-origin/dev}^{commit}" 2>/dev/null || printf unknown)"
  [[ "$base" =~ ^[0-9a-f]{40,64}$ ]] || base=unknown
  load="$(loadavg_per_cpu)"
  if [[ "$commit" == "unknown" || "$load" == "null" ]]; then status=observation; fi
  elapsed_seconds="$(awk -v value="$elapsed_ms" 'BEGIN {printf "%.3f", value / 1000}')"
  rss_peak_mb="$(awk -v value="$RSS_PEAK_KB" 'BEGIN {printf "%.3f", value / 1024}')"
  printf '{"schema":"stratalint-perf-event-v1","run_id":"report-%s-%s","ts":"%s","cohort":{"venue":"%s","os":"%s","arch":"%s","cpu_class":"%s","runner_class":null},"context":{"commit":"%s","base":"%s","workload_id":"report","cache_state":null,"loadavg_per_cpu":%s,"host_concurrency":%s},"kind":"resource","stage":"%s","status":"%s","elapsed_seconds":%s,"resources":{"disk_free_gb":null,"fd_peak":%s,"rss_peak_mb":%s},"role":"%s","pid":%s,"elapsed_ms":%s,"rc":%s,"fd_peak":%s,"rss_peak_kb":%s,"concurrency_count":%s}\n' \
    "$STARTED_MS" "$CHILD_PID" "$timestamp" "$venue" "$os" "$arch" "$arch" \
    "$commit" "$base" "$load" "$CONCURRENCY_COUNT" "$ROLE" "$status" \
    "$elapsed_seconds" "$FD_PEAK" "$rss_peak_mb" "$ROLE" "$CHILD_PID" \
    "$elapsed_ms" "$rc" "$FD_PEAK" "$RSS_PEAK_KB" "$CONCURRENCY_COUNT"
}

acquire_metrics_lock() {
  local deadline=$(( $(date +%s) + LOCK_TIMEOUT_SECONDS ))
  METRICS_LOCK_DIR="${METRICS_LOG}.lock"
  while ! mkdir "$METRICS_LOCK_DIR" 2>/dev/null; do
    reclaim_stale_lock "$METRICS_LOCK_DIR" || true
    if (( $(date +%s) >= deadline )); then
      echo "report-supervisor: timed out waiting for the performance ledger" >&2
      return 2
    fi
    sleep 0.05
  done
  printf '%s\n' "$$" > "$METRICS_LOCK_DIR/owner" \
    || { echo "report-supervisor: could not record performance ledger owner" >&2; return 2; }
}

append_metrics() {
  local rc="$1"
  local elapsed_ms="$2"
  local ledger_tmp=""
  acquire_metrics_lock || return 2
  ledger_tmp="$(mktemp "$(dirname "$METRICS_LOG")/.events.XXXXXXXX")" || return 2
  if [[ -e "$METRICS_LOG" && ! -f "$METRICS_LOG" ]]; then
    rm -f -- "$ledger_tmp"
    return 2
  fi
  if [[ -f "$METRICS_LOG" ]]; then
    cat "$METRICS_LOG" > "$ledger_tmp" || { rm -f -- "$ledger_tmp"; return 2; }
  fi
  performance_event "$rc" "$elapsed_ms" >> "$ledger_tmp" \
    || { rm -f -- "$ledger_tmp"; return 2; }
  mv -f -- "$ledger_tmp" "$METRICS_LOG" || { rm -f -- "$ledger_tmp"; return 2; }
  rm -rf -- "$METRICS_LOCK_DIR"
  METRICS_LOCK_DIR=""
}

finish() {
  local rc=$?
  local finished_ms
  local metrics_rc=0
  trap - EXIT HUP INT TERM
  set +e
  if [[ -n "$PROCESS_GROUP_ID" ]]; then
    sample_process_tree
    terminate_process_group "$PROCESS_GROUP_ID"
  fi
  if [[ -n "$CHILD_PID" ]]; then
    wait "$CHILD_PID" >/dev/null 2>&1 || true
  fi
  finished_ms="$(now_ms)"
  if [[ -n "$CHILD_PID" && "$STARTED_MS" -gt 0 ]]; then
    append_metrics "$rc" "$((finished_ms - STARTED_MS))" || metrics_rc=$?
    if [[ "$metrics_rc" -ne 0 ]]; then
      echo "report-supervisor: performance event commit failed" >&2
      if [[ "$rc" -eq 0 ]]; then rc=2; fi
    fi
  fi
  if [[ -n "$METRICS_LOCK_DIR" ]]; then rm -rf -- "$METRICS_LOCK_DIR"; fi
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
