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
CALLER_WORKTREE=""
if (( LEAN_SLOT )); then
  CALLER_WORKTREE="$(pwd -P)" \
    || { echo "report-supervisor: could not identify the caller working directory" >&2; exit 2; }
  [[ "$CALLER_WORKTREE" != *$'\n'* && "$CALLER_WORKTREE" != *$'\r'* ]] \
    || { echo "report-supervisor: caller working directory must not contain line breaks" >&2; exit 2; }
fi

REPOSITORY_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd -P)"
PERF_EVENT_LIB="$REPOSITORY_ROOT/Meta/StrataLint/scripts/perf-event-lib.sh"
[[ -r "$PERF_EVENT_LIB" ]] || exit 2
source "$PERF_EVENT_LIB"
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
# Wall-clock budget for the worker build itself (#403): a build that hangs while
# holding the lean slot would otherwise loop the monitor below forever, never
# reaching finish() (which releases the slot), starving every subsequent lean
# build. 0 disables the bound (legacy unbounded behavior). Default is generous
# enough for any legitimate lean-report build yet finite so a hang self-releases.
BUILD_TIMEOUT_SECONDS="${STRATALINT_BUILD_TIMEOUT_SECONDS:-7200}"
[[ "$BUILD_TIMEOUT_SECONDS" =~ ^[0-9]+$ && "$BUILD_TIMEOUT_SECONDS" -le 86400 ]] \
  || { echo "report-supervisor: STRATALINT_BUILD_TIMEOUT_SECONDS must be 0..86400" >&2; exit 2; }
LOCK_INITIALIZATION_GRACE_SECONDS=5

TMP_ROOT=""
CHILD_PID=""
PROCESS_GROUP_ID=""
PROCESS_CANDIDATES_FILE=""
STDOUT_RELAY_PID=""
STDERR_RELAY_PID=""
SLOT_DIR=""
METRICS_LOCK_DIR=""
CONCURRENCY_COUNT=0
FD_PEAK=0
RSS_PEAK_KB=0
STARTED_MS=0

early_cleanup() {
  if [[ -n "$TMP_ROOT" ]]; then rm -rf -- "$TMP_ROOT"; fi
}
trap early_cleanup EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

mkdir -p "$RUN_ROOT" "$SLOT_ROOT" "$(dirname "$METRICS_LOG")"
TMP_ROOT="$(mktemp -d "$RUN_ROOT/run.XXXXXXXX")"
TMP_ROOT="$(cd "$TMP_ROOT" && pwd -P)"
SCRATCH="$TMP_ROOT/scratch"
mkdir -p "$SCRATCH"
RUN_STDOUT="$TMP_ROOT/stdout.pipe"
RUN_STDERR="$TMP_ROOT/stderr.pipe"
RUN_MARKER="$TMP_ROOT/process.marker"
PROCESS_CANDIDATES_FILE="$TMP_ROOT/process-candidates"
mkfifo "$RUN_STDOUT" "$RUN_STDERR"
: > "$RUN_MARKER"
: > "$PROCESS_CANDIDATES_FILE"
if [[ ! -d /proc ]] && ! command -v lsof >/dev/null 2>&1; then
  echo "report-supervisor: lsof is required for process supervision on this host" >&2
  exit 2
fi

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

process_start_identity() {
  ps -o lstart= -p "$1" 2>/dev/null | awk '{$1=$1; print; exit}'
}

owner_identity() {
  local start
  start="$(process_start_identity "$$")"
  [[ -n "$start" ]] || return 1
  printf '%s|%s\n' "$$" "$start"
}

lock_is_stale() {
  local lock="$1"
  local owner=""
  local pid=""
  local expected_start=""
  local actual_start=""
  local mtime=""
  if [[ -f "$lock/owner" ]]; then
    read -r owner < "$lock/owner" || owner=""
  fi
  if [[ "$owner" =~ ^([1-9][0-9]*)\|(.*)$ ]]; then
    pid="${BASH_REMATCH[1]}"
    expected_start="${BASH_REMATCH[2]}"
    process_exists "$pid" || return 0
    actual_start="$(process_start_identity "$pid")"
    [[ -n "$actual_start" && "$actual_start" == "$expected_start" ]] && return 1
    return 0
  fi
  if [[ "$owner" =~ ^[1-9][0-9]*$ ]]; then
    process_exists "$owner" && return 1
    return 0
  fi
  mtime="$(lock_mtime "$lock" || true)"
  [[ "$mtime" =~ ^[0-9]+$ ]] || return 1
  (( $(date +%s) - mtime >= LOCK_INITIALIZATION_GRACE_SECONDS ))
}

reclaim_lock_without_guard() {
  local lock="$1"
  lock_is_stale "$lock" || return 1
  local stale="${lock}.stale.$$.$RANDOM"
  if mv "$lock" "$stale" 2>/dev/null; then
    rm -rf -- "$stale"
    return 0
  fi
  return 1
}

acquire_lock_guard() {
  local lock="$1"
  local guard="${lock}.reclaim-guard"
  local deadline=$(( $(date +%s) + LOCK_TIMEOUT_SECONDS ))
  local identity
  identity="$(owner_identity)" \
    || { echo "report-supervisor: could not identify lock owner process" >&2; return 2; }
  while ! mkdir "$guard" 2>/dev/null; do
    reclaim_lock_without_guard "$guard" || true
    if (( $(date +%s) >= deadline )); then return 2; fi
    sleep 0.05
  done
  if ! printf '%s\n' "$identity" > "$guard/owner"; then
    rm -rf -- "$guard"
    return 2
  fi
}

release_lock_guard() {
  rm -rf -- "${1}.reclaim-guard"
}

reclaim_stale_lock() {
  local lock="$1"
  acquire_lock_guard "$lock" || return 1
  reclaim_lock_without_guard "$lock"
  local rc=$?
  release_lock_guard "$lock"
  return "$rc"
}

claim_lock() {
  local lock="$1"
  local record_holder_metadata="${2:-0}"
  local identity
  local acquired_metadata
  local acquired_at_epoch
  local acquired_at
  identity="$(owner_identity)" \
    || { echo "report-supervisor: could not identify lock owner process" >&2; return 2; }
  acquire_lock_guard "$lock" || return 1
  if ! mkdir "$lock" 2>/dev/null; then
    release_lock_guard "$lock"
    return 1
  fi
  if ! printf '%s\n' "$identity" > "$lock/owner"; then
    rm -rf -- "$lock"
    release_lock_guard "$lock"
    return 2
  fi
  if (( record_holder_metadata )); then
    acquired_metadata="$(date -u '+%s|%Y-%m-%dT%H:%M:%SZ')" || acquired_metadata=""
    acquired_at_epoch="${acquired_metadata%%|*}"
    acquired_at="${acquired_metadata#*|}"
    if [[ ! "$acquired_at_epoch" =~ ^[0-9]+$ \
      || ! "$acquired_at" =~ ^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z$ ]] \
      || ! {
        printf '%s\n' "$ROLE" > "$lock/role" \
          && printf '%s\n' "$CALLER_WORKTREE" > "$lock/worktree" \
          && printf '%s\n' "$acquired_at" > "$lock/acquired-at" \
          && printf '%s\n' "$acquired_at_epoch" > "$lock/acquired-at-epoch"
      }; then
      rm -rf -- "$lock"
      release_lock_guard "$lock"
      return 2
    fi
  fi
  release_lock_guard "$lock"
}

active_slot_count() {
  find "$SLOT_ROOT" -maxdepth 1 -type d -name 'slot-*.lock' -print 2>/dev/null \
    | awk 'END {print NR + 0}'
}

read_lock_field() {
  local lock="$1"
  local name="$2"
  local value=""
  [[ -f "$lock/$name" ]] || return 1
  IFS= read -r value < "$lock/$name" || true
  [[ -n "$value" ]] || return 1
  printf '%s' "$value"
}

report_lean_slot_holder() {
  local lock="$1"
  local identity
  local confirmed_identity
  local role
  local worktree
  local acquired_at
  local acquired_at_epoch
  local held_seconds="unknown"
  local now

  identity="$(read_lock_field "$lock" owner || true)"
  role="$(read_lock_field "$lock" role || true)"
  worktree="$(read_lock_field "$lock" worktree || true)"
  acquired_at="$(read_lock_field "$lock" acquired-at || true)"
  acquired_at_epoch="$(read_lock_field "$lock" acquired-at-epoch || true)"
  confirmed_identity="$(read_lock_field "$lock" owner || true)"

  if [[ -z "$identity" || "$identity" != "$confirmed_identity" || ! -d "$lock" ]]; then
    identity="unknown"
    role="unknown"
    worktree="unknown"
    acquired_at="unknown"
    acquired_at_epoch=""
  fi
  [[ "$role" =~ ^[a-z0-9][a-z0-9-]*$ ]] || role="unknown"
  [[ "$worktree" == /* ]] || worktree="unknown"
  [[ "$acquired_at" =~ ^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z$ ]] \
    || acquired_at="unknown"
  now="$(date +%s)"
  if [[ "$acquired_at_epoch" =~ ^[0-9]+$ && "$now" =~ ^[0-9]+$ \
    && "$acquired_at_epoch" -le "$now" ]]; then
    held_seconds=$((now - acquired_at_epoch))
  fi

  printf 'report-supervisor: Lean slot holder slot=%q identity=%q acquired_at=%q held_seconds=%q role=%q worktree=%q\n' \
    "${lock##*/}" "$identity" "$acquired_at" "$held_seconds" "$role" "$worktree" >&2
}

report_lean_slot_holders() {
  local index
  local lock
  local found=0
  for ((index = 1; index <= MAX_CONCURRENCY; index++)); do
    lock="$SLOT_ROOT/slot-$index.lock"
    [[ -d "$lock" ]] || continue
    found=1
    report_lean_slot_holder "$lock"
  done
  if (( found == 0 )); then
    echo "report-supervisor: Lean slot holder metadata unavailable" >&2
  fi
}

acquire_lean_slot() {
  local index
  local candidate
  local deadline=$(( $(date +%s) + LOCK_TIMEOUT_SECONDS ))
  while true; do
    for ((index = 1; index <= MAX_CONCURRENCY; index++)); do
      candidate="$SLOT_ROOT/slot-$index.lock"
      if claim_lock "$candidate" 1; then
        SLOT_DIR="$candidate"
        CONCURRENCY_COUNT="$(active_slot_count)"
        return 0
      fi
      reclaim_stale_lock "$candidate" || true
    done
    if (( $(date +%s) >= deadline )); then
      echo "report-supervisor: timed out waiting for a Lean slot" >&2
      report_lean_slot_holders
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

marker_processes() {
  local process_dir fd target pid candidates elapsed_window
  if [[ -d /proc ]]; then
    for process_dir in /proc/[1-9]*; do
      [[ -d "$process_dir/fd" ]] || continue
      pid="${process_dir##*/}"
      # Workers inherit the two relay pipes and the dedicated marker on fd 9.
      for fd in "$process_dir"/fd/1 "$process_dir"/fd/2 "$process_dir"/fd/9; do
        [[ -e "$fd" || -L "$fd" ]] || continue
        target="$(readlink "$fd" 2>/dev/null || true)"
        if [[ "$target" == "$RUN_STDOUT" \
          || "$target" == "$RUN_STDERR" \
          || "$target" == "$RUN_MARKER" ]]; then
          printf '%s\n' "$pid"
          break
        fi
      done
    done
  else
    elapsed_window=$(( ($(now_ms) - STARTED_MS) / 1000 + 5 ))
    candidates="$(ps -axo pid=,ppid=,etime= 2>/dev/null \
      | awk -v window="$elapsed_window" '
          function elapsed(value, fields, count, hour) {
            count = split(value, fields, ":")
            seconds = fields[count] + 0
            if (count >= 2) seconds += 60 * fields[count - 1]
            if (count >= 3) {
              hour = fields[count - 2]
              if (hour ~ /-/) {
                split(hour, day_hour, "-")
                seconds += 86400 * day_hour[1] + 3600 * day_hour[2]
              } else {
                seconds += 3600 * hour
              }
            }
            return seconds
          }
          $2 == 1 && elapsed($3) <= window {print $1}
        ' | paste -sd, -)"
    [[ -n "$candidates" ]] || return 0
    # lsof exits non-zero when a candidate pid vanished between ps and lsof (a
    # routine race under short-lived build children); with set -euo pipefail
    # that killed the supervisor, whose EXIT trap then TERM'd the healthy child
    # process group — the drifting-kill-site ceremony deaths of #570.
    { lsof -a -p "$candidates" -d 1,2,9 2>/dev/null || true; } \
      | awk -v stdout="$RUN_STDOUT" -v stderr="$RUN_STDERR" -v marker="$RUN_MARKER" \
          '$NF == stdout || $NF == stderr || $NF == marker {print $2}'
  fi
}

signal_marker_processes() {
  local signal="$1"
  local pid
  {
    if [[ -n "$CHILD_PID" ]]; then collect_process_tree "$CHILD_PID"; fi
    marker_processes
  } | sort -run | while IFS= read -r pid; do
    [[ "$pid" =~ ^[1-9][0-9]*$ \
      && "$pid" != "$$" \
      && "$pid" != "$STDOUT_RELAY_PID" \
      && "$pid" != "$STDERR_RELAY_PID" ]] || continue
    kill "-$signal" "$pid" >/dev/null 2>&1 || true
  done
}

remember_process_candidate() {
  local pid="$1"
  local identity=""
  [[ "$pid" =~ ^[1-9][0-9]*$ ]] || return 0
  identity="$(process_start_identity "$pid")" || return 0
  [[ -n "$identity" ]] || return 0
  grep -Fqx -- "$pid|$identity" "$PROCESS_CANDIDATES_FILE" 2>/dev/null \
    || printf '%s|%s\n' "$pid" "$identity" >> "$PROCESS_CANDIDATES_FILE"
}

record_process_candidates() {
  local pid
  while IFS= read -r pid; do
    remember_process_candidate "$pid"
  done
}

record_supervised_processes() {
  {
    if [[ -n "$CHILD_PID" ]]; then collect_process_tree "$CHILD_PID"; fi
    marker_processes
  } | sort -un | record_process_candidates
}

signal_recorded_processes() {
  local signal="$1"
  local pid identity current_identity
  [[ -f "$PROCESS_CANDIDATES_FILE" ]] || return 0
  while IFS='|' read -r pid identity; do
    [[ "$pid" =~ ^[1-9][0-9]*$ \
      && -n "$identity" \
      && "$pid" != "$$" \
      && "$pid" != "$STDOUT_RELAY_PID" \
      && "$pid" != "$STDERR_RELAY_PID" ]] || continue
    current_identity="$(process_start_identity "$pid")" || continue
    [[ "$current_identity" == "$identity" ]] || continue
    kill "-$signal" "$pid" >/dev/null 2>&1 || true
  done < <(sort -t '|' -k1,1nr "$PROCESS_CANDIDATES_FILE")
}

sample_process_tree() {
  local pid rss fd members
  local rss_total=0
  local fd_total=0
  members="$({
    if [[ -n "$CHILD_PID" ]]; then collect_process_tree "$CHILD_PID"; fi
    marker_processes
  } | sort -un)"
  record_process_candidates <<< "$members"
  while IFS= read -r pid; do
    [[ -n "$pid" \
      && "$pid" != "$STDOUT_RELAY_PID" \
      && "$pid" != "$STDERR_RELAY_PID" ]] || continue
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
  done <<< "$members"
  if [[ "$rss_total" -gt "$RSS_PEAK_KB" ]]; then RSS_PEAK_KB="$rss_total"; fi
  if [[ "$fd_total" -gt "$FD_PEAK" ]]; then FD_PEAK="$fd_total"; fi
}

terminate_process_group() {
  local group_id="$1"
  record_supervised_processes
  signal_recorded_processes TERM
  signal_marker_processes TERM
  kill -TERM -- "-$group_id" >/dev/null 2>&1 || true
  sleep 0.2
  record_supervised_processes
  signal_recorded_processes KILL
  signal_marker_processes KILL
  kill -KILL -- "-$group_id" >/dev/null 2>&1 || true
}

wait_for_relay() {
  local pid="$1"
  local deadline=$(( $(date +%s) + 2 ))
  local state=""
  while process_exists "$pid"; do
    state="$(ps -o stat= -p "$pid" 2>/dev/null | awk '{$1=$1; print; exit}')"
    if [[ -z "$state" || "$state" == Z* ]]; then break; fi
    if (( $(date +%s) >= deadline )); then
      kill -TERM "$pid" >/dev/null 2>&1 || true
      sleep 0.1
      kill -KILL "$pid" >/dev/null 2>&1 || true
      break
    fi
    sleep 0.05
  done
  wait "$pid" >/dev/null 2>&1 || true
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
  local timestamp status venue os arch cpu_class commit base load elapsed_seconds rss_peak_mb
  timestamp="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  status=observation
  venue=local
  if [[ "${CI:-}" == "true" || "${CI:-}" == "1" ]]; then venue=ci; fi
  os="$(uname -s 2>/dev/null || printf unknown)"
  arch="$(uname -m 2>/dev/null || printf unknown)"
  cpu_class=""
  if command -v sysctl >/dev/null 2>&1; then
    cpu_class="$(sysctl -n machdep.cpu.brand_string 2>/dev/null || true)"
  fi
  if [[ -z "$cpu_class" && -r /proc/cpuinfo ]]; then
    cpu_class="$(awk -F ': *' '/^model name/ {print $2; exit}' /proc/cpuinfo)"
  fi
  if [[ -z "$cpu_class" ]]; then cpu_class="$arch"; fi
  cpu_class="$(printf '%s' "$cpu_class" | sed 's/["\\]/_/g')"
  commit="$(git -C "$REPOSITORY_ROOT" rev-parse --verify 'HEAD^{commit}' 2>/dev/null || printf unknown)"
  [[ "$commit" =~ ^[0-9a-f]{40,64}$ ]] || commit=unknown
  base="$(git -C "$REPOSITORY_ROOT" rev-parse --verify "${STRATALINT_PERF_BASE:-origin/dev}^{commit}" 2>/dev/null || printf unknown)"
  [[ "$base" =~ ^[0-9a-f]{40,64}$ ]] || base=unknown
  load="$(perf_json_nonnegative_number_or_null "$(loadavg_per_cpu)")"
  elapsed_seconds="$(awk -v value="$elapsed_ms" 'BEGIN {printf "%.3f", value / 1000}')"
  rss_peak_mb="$(awk -v value="$RSS_PEAK_KB" 'BEGIN {printf "%.3f", value / 1024}')"
  printf '{"schema":"stratalint-perf-event-v1","run_id":"report-%s-%s","ts":"%s","cohort":{"venue":"%s","os":"%s","arch":"%s","cpu_class":"%s","runner_class":null},"context":{"commit":"%s","base":"%s","workload_id":"report","cache_state":null,"loadavg_per_cpu":%s,"host_concurrency":null},"kind":"resource","stage":"%s","status":"%s","elapsed_seconds":%s,"resources":{"disk_free_gb":null,"fd_peak":%s,"rss_peak_mb":%s},"role":"%s","pid":%s,"elapsed_ms":%s,"rc":%s,"fd_peak":%s,"rss_peak_kb":%s,"concurrency_count":%s}\n' \
    "$STARTED_MS" "$CHILD_PID" "$timestamp" "$venue" "$os" "$arch" "$cpu_class" \
    "$commit" "$base" "$load" "$ROLE" "$status" \
    "$elapsed_seconds" "$FD_PEAK" "$rss_peak_mb" "$ROLE" "$CHILD_PID" \
    "$elapsed_ms" "$rc" "$FD_PEAK" "$RSS_PEAK_KB" "$CONCURRENCY_COUNT"
}

acquire_metrics_lock() {
  local deadline=$(( $(date +%s) + LOCK_TIMEOUT_SECONDS ))
  local candidate="${METRICS_LOG}.lock"
  while ! claim_lock "$candidate"; do
    reclaim_stale_lock "$candidate" || true
    if (( $(date +%s) >= deadline )); then
      echo "report-supervisor: timed out waiting for the performance ledger" >&2
      return 2
    fi
    sleep 0.05
  done
  METRICS_LOCK_DIR="$candidate"
}

append_metrics() {
  local rc="$1"
  local elapsed_ms="$2"
  local event_tmp=""
  acquire_metrics_lock || return 2
  event_tmp="$(mktemp "$TMP_ROOT/event.XXXXXXXX")" || return 2
  performance_event "$rc" "$elapsed_ms" > "$event_tmp" \
    || { rm -f -- "$event_tmp"; return 2; }
  ( trap '' XFSZ
    STRATALINT_PERF_LEDGER="$METRICS_LOG" \
      perf_flush_events "$REPOSITORY_ROOT" "$event_tmp" >/dev/null 2>&1
  ) \
    || { rm -f -- "$event_tmp"; return 2; }
  rm -f -- "$event_tmp"
  rm -rf -- "$METRICS_LOCK_DIR"
  METRICS_LOCK_DIR=""
}

finish() {
  local rc=$?
  local finished_ms
  trap - EXIT HUP INT TERM
  set +e
  if [[ -n "$PROCESS_GROUP_ID" ]]; then
    sample_process_tree
    terminate_process_group "$PROCESS_GROUP_ID"
  fi
  if [[ -n "$CHILD_PID" ]]; then
    wait "$CHILD_PID" >/dev/null 2>&1 || true
  fi
  if [[ -n "$STDOUT_RELAY_PID" ]]; then wait_for_relay "$STDOUT_RELAY_PID"; fi
  if [[ -n "$STDERR_RELAY_PID" ]]; then wait_for_relay "$STDERR_RELAY_PID"; fi
  finished_ms="$(now_ms)"
  if [[ -n "$CHILD_PID" && "$STARTED_MS" -gt 0 ]]; then
    append_metrics "$rc" "$((finished_ms - STARTED_MS))" >/dev/null 2>&1 || true
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
cat "$RUN_STDOUT" &
STDOUT_RELAY_PID=$!
cat "$RUN_STDERR" >&2 &
STDERR_RELAY_PID=$!
set -m
TMPDIR="$SCRATCH" "$@" 9< "$RUN_MARKER" > "$RUN_STDOUT" 2> "$RUN_STDERR" &
CHILD_PID=$!
PROCESS_GROUP_ID="$CHILD_PID"
set +m
BUILD_DEADLINE=0
if (( BUILD_TIMEOUT_SECONDS > 0 )); then
  BUILD_DEADLINE=$(( $(date +%s) + BUILD_TIMEOUT_SECONDS ))
fi
BUILD_TIMED_OUT=0
while process_exists "$CHILD_PID"; do
  sample_process_tree
  if (( BUILD_DEADLINE > 0 )) && (( $(date +%s) >= BUILD_DEADLINE )); then
    echo "report-supervisor: build exceeded ${BUILD_TIMEOUT_SECONDS}s wall-clock budget;" \
      "terminating to release the lean slot (#403)" >&2
    terminate_process_group "$PROCESS_GROUP_ID"
    BUILD_TIMED_OUT=1
    break
  fi
  sleep 0.1
done
set +e
wait "$CHILD_PID"
rc=$?
set -e
if [[ "$BUILD_TIMED_OUT" == "1" ]]; then rc=124; fi
exit "$rc"
