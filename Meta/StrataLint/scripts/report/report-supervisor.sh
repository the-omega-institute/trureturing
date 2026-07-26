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

REPOSITORY_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd -P)"
PERF_EVENT_LIB="$REPOSITORY_ROOT/Meta/StrataLint/scripts/perf-event-lib.sh"
PROCESS_CONTROL_LIB="$REPOSITORY_ROOT/Meta/StrataLint/scripts/report/report-process-control.sh"
[[ -r "$PERF_EVENT_LIB" && -r "$PROCESS_CONTROL_LIB" ]] || exit 2
source "$PERF_EVENT_LIB"
source "$PROCESS_CONTROL_LIB"
PROCESS_FS_ROOT=/proc
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
STALL_WINDOW_SECONDS="${STRATALINT_REPORT_STALL_WINDOW_SECONDS:-60}"
[[ "$STALL_WINDOW_SECONDS" =~ ^[1-9][0-9]*$ \
  && "$STALL_WINDOW_SECONDS" -le 86400 ]] \
  || { echo "report-supervisor: STRATALINT_REPORT_STALL_WINDOW_SECONDS must be 1..86400" >&2; exit 2; }
STALL_WINDOW_COUNT="${STRATALINT_REPORT_STALL_WINDOW_COUNT:-3}"
[[ "$STALL_WINDOW_COUNT" =~ ^[1-9][0-9]*$ \
  && "$STALL_WINDOW_COUNT" -le 100 ]] \
  || { echo "report-supervisor: STRATALINT_REPORT_STALL_WINDOW_COUNT must be 1..100" >&2; exit 2; }
OBSERVATION_POLL_SECONDS="${STRATALINT_REPORT_OBSERVATION_POLL_SECONDS:-5}"
[[ "$OBSERVATION_POLL_SECONDS" =~ ^[1-9][0-9]*$ && "$OBSERVATION_POLL_SECONDS" -le 300 ]] \
  || { echo "report-supervisor: STRATALINT_REPORT_OBSERVATION_POLL_SECONDS must be 1..300" >&2; exit 2; }
PROGRESS_ROOT="${STRATALINT_LEAN_PROGRESS_ROOT:-$PWD}"
[[ "$LEAN_SLOT" == "0" || ( "$PROGRESS_ROOT" == /* && -d "$PROGRESS_ROOT" ) ]] \
  || { echo "report-supervisor: STRATALINT_LEAN_PROGRESS_ROOT must be an absolute directory" >&2; exit 2; }
PROGRESS_LOG_ROOT="${STRATALINT_LEAN_PROGRESS_LOG_ROOT:-}"
[[ "$LEAN_SLOT" == "0" || -z "$PROGRESS_LOG_ROOT" || "$PROGRESS_LOG_ROOT" == /* ]] \
  || { echo "report-supervisor: STRATALINT_LEAN_PROGRESS_LOG_ROOT must be absolute when set" >&2; exit 2; }
# Wall-clock budget for the worker build itself (#403): a build that hangs while
# holding the lean slot would otherwise loop the monitor below forever, never
# reaching finish() (which releases the slot), starving every subsequent lean
# build. 0 disables the bound (legacy unbounded behavior). Default is generous
# enough for any legitimate lean-report build yet finite so a hang self-releases.
BUILD_TIMEOUT_SECONDS="${STRATALINT_BUILD_TIMEOUT_SECONDS:-7200}"
[[ "$BUILD_TIMEOUT_SECONDS" =~ ^[0-9]+$ && "$BUILD_TIMEOUT_SECONDS" -le 86400 ]] \
  || { echo "report-supervisor: STRATALINT_BUILD_TIMEOUT_SECONDS must be 0..86400" >&2; exit 2; }

TMP_ROOT=""
CHILD_PID=""
PROCESS_GROUP_ID=""
PROCESS_GROUP_START_IDENTITY=""
STDOUT_RELAY_PID=""
STDERR_RELAY_PID=""
SLOT_DIR=""
SLOT_OWNER_BASE=""
METRICS_LOCK_DIR=""
CONCURRENCY_COUNT=0
FD_PEAK=0
RSS_PEAK_KB=0
STARTED_MS=0
LAST_OBSERVATION_CHECK=0
OBSERVATION_WINDOW_STARTED_SECONDS=0
LAST_CPU_SNAPSHOT=0
LAST_SIGNAL_SNAPSHOT=""
OBSERVATION_WINDOW_CPU_CHANGED=0
OBSERVATION_WINDOW_SIGNAL_CHANGED=0
CONSECUTIVE_STALLED_WINDOWS=0
OBSERVATION_DISABLED=0
CLAIMED_OWNER_BASE=""
ACTIVE_GUARD_PATH=""
ACTIVE_GUARD_TOKEN=""

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
mkfifo "$RUN_STDOUT" "$RUN_STDERR"
: > "$RUN_MARKER"
if [[ ! -d "$PROCESS_FS_ROOT" ]] && ! command -v lsof >/dev/null 2>&1; then
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

lock_mtime() {
  local value=""
  value="$(stat -f '%m' "$1" 2>/dev/null || true)"
  if [[ "$value" =~ ^[0-9]+$ ]]; then printf '%s\n' "$value"; return 0; fi
  value="$(stat -c '%Y' "$1" 2>/dev/null || true)"
  [[ "$value" =~ ^[0-9]+$ ]] || return 1
  printf '%s\n' "$value"
}

file_size() {
  local value=""
  value="$(stat -f '%z' "$1" 2>/dev/null || true)"
  if [[ "$value" =~ ^[0-9]+$ ]]; then printf '%s\n' "$value"; return 0; fi
  value="$(stat -c '%s' "$1" 2>/dev/null || true)"
  [[ "$value" =~ ^[0-9]+$ ]] || return 1
  printf '%s\n' "$value"
}

owner_base_identity() {
  local start
  start="$(process_start_identity "$$" || true)"
  if [[ -z "$start" ]]; then start=unknown; fi
  printf '%s|%s\n' "$$" "$start"
}

write_lock_owner() {
  local lock="$1"
  local base="$2"
  local temporary="$lock/.owner.$$.$RANDOM"
  printf '%s|%s\n' "$base" "$(now_ms)" > "$temporary" || return 1
  mv -f -- "$temporary" "$lock/owner"
}

lock_is_owned_by() {
  local lock="$1"
  local expected="$2"
  local owner=""
  [[ -f "$lock/owner" ]] || return 1
  read -r owner < "$lock/owner" || return 1
  [[ "$owner" =~ ^(.*)\|([0-9]+)$ && "${BASH_REMATCH[1]}" == "$expected" ]]
}

lock_is_stale() {
  local lock="$1"
  local owner_path="$lock/owner"
  local owner=""
  local pid=""
  local expected_start=""
  local actual_start=""
  local exists_rc=0
  if [[ ! -e "$owner_path" && ! -L "$owner_path" ]]; then
    # mkdir publishes a reclaim guard before its owner record is atomically
    # renamed into place. Only that absent path is a pollable publication gap.
    [[ "$lock" == *.reclaim-guard ]] && return 1
    return 2
  fi
  [[ -f "$owner_path" ]] || return 2
  read -r owner < "$owner_path" || return 2
  [[ -n "$owner" ]] || return 2
  if [[ "$owner" =~ ^([1-9][0-9]*)\|([^|]+)\|([0-9]+)$ ]]; then
    pid="${BASH_REMATCH[1]}"
    expected_start="${BASH_REMATCH[2]}"
    if process_exists "$pid"; then
      :
    else
      exists_rc=$?
      [[ "$exists_rc" == "2" ]] && return 2
      stale_slot_is_quiescent "$lock"
      return $?
    fi
    if [[ "$expected_start" == "unknown" ]]; then
      return 2
    fi
    actual_start="$(process_start_identity "$pid")" || return 2
    [[ -n "$actual_start" ]] || return 2
    if [[ "$actual_start" != "$expected_start" ]]; then
      stale_slot_is_quiescent "$lock"
      return $?
    fi
    return 1
  fi
  if [[ "$owner" =~ ^([1-9][0-9]*)\|([^|]+)$ ]]; then
    pid="${BASH_REMATCH[1]}"
    expected_start="${BASH_REMATCH[2]}"
    if process_exists "$pid"; then
      :
    else
      exists_rc=$?
      [[ "$exists_rc" == "2" ]] && return 2
      stale_slot_is_quiescent "$lock"
      return $?
    fi
    actual_start="$(process_start_identity "$pid")" || return 2
    [[ -n "$actual_start" ]] || return 2
    if [[ "$actual_start" != "$expected_start" ]]; then
      stale_slot_is_quiescent "$lock"
      return $?
    fi
    return 1
  fi
  if [[ "$owner" =~ ^[1-9][0-9]*$ ]]; then
    if process_exists "$owner"; then
      :
    else
      exists_rc=$?
      [[ "$exists_rc" == "2" ]] && return 2
      stale_slot_is_quiescent "$lock"
      return $?
    fi
    return 1
  fi
  return 2
}

reclaim_lock_without_guard() {
  local lock="$1"
  local stale_rc=0
  if lock_is_stale "$lock"; then
    :
  else
    stale_rc=$?
    return "$stale_rc"
  fi
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
  local reclaim_rc=0
  identity="$(owner_base_identity)" \
    || { echo "report-supervisor: could not identify lock owner process" >&2; return 2; }
  while ! mkdir "$guard" 2>/dev/null; do
    if reclaim_lock_without_guard "$guard"; then
      :
    else
      reclaim_rc=$?
      [[ "$reclaim_rc" == "2" ]] && return 2
    fi
    if (( $(date +%s) >= deadline )); then return 2; fi
    sleep 0.05
  done
  if ! write_lock_owner "$guard" "$identity"; then
    rm -rf -- "$guard"
    return 2
  fi
  ACTIVE_GUARD_PATH="$guard"
  ACTIVE_GUARD_TOKEN="$$.$RANDOM.$(now_ms)"
  if ! printf '%s\n' "$ACTIVE_GUARD_TOKEN" > "$guard/token"; then
    rm -rf -- "$guard"
    ACTIVE_GUARD_PATH=""
    ACTIVE_GUARD_TOKEN=""
    return 2
  fi
}

release_lock_guard() {
  local guard="${1}.reclaim-guard"
  local token=""
  if [[ "$ACTIVE_GUARD_PATH" == "$guard" && -f "$guard/token" ]]; then
    read -r token < "$guard/token" || token=""
    if [[ -n "$token" && "$token" == "$ACTIVE_GUARD_TOKEN" ]]; then
      rm -rf -- "$guard"
    fi
  fi
  ACTIVE_GUARD_PATH=""
  ACTIVE_GUARD_TOKEN=""
}

reclaim_stale_lock() {
  local lock="$1"
  local guard_rc=0
  if acquire_lock_guard "$lock"; then
    :
  else
    guard_rc=$?
    return "$guard_rc"
  fi
  reclaim_lock_without_guard "$lock"
  local rc=$?
  release_lock_guard "$lock"
  return "$rc"
}

claim_lock() {
  local lock="$1"
  local identity
  local guard_rc=0
  identity="$(owner_base_identity)" \
    || { echo "report-supervisor: could not identify lock owner process" >&2; return 2; }
  if acquire_lock_guard "$lock"; then
    :
  else
    guard_rc=$?
    return "$guard_rc"
  fi
  if ! mkdir "$lock" 2>/dev/null; then
    release_lock_guard "$lock"
    return 1
  fi
  if ! write_lock_owner "$lock" "$identity"; then
    rm -rf -- "$lock"
    release_lock_guard "$lock"
    return 2
  fi
  CLAIMED_OWNER_BASE="$identity"
  release_lock_guard "$lock"
}

active_slot_count() {
  find "$SLOT_ROOT" -maxdepth 1 -type d -name 'slot-*.lock' -print 2>/dev/null \
    | awk 'END {print NR + 0}'
}

acquire_lean_slot() {
  local index
  local candidate
  local claim_rc
  local reclaim_rc
  local deadline=$(( $(date +%s) + LOCK_TIMEOUT_SECONDS ))
  while true; do
    for ((index = 1; index <= MAX_CONCURRENCY; index++)); do
      candidate="$SLOT_ROOT/slot-$index.lock"
      if claim_lock "$candidate"; then
        SLOT_DIR="$candidate"
        SLOT_OWNER_BASE="$CLAIMED_OWNER_BASE"
        CONCURRENCY_COUNT="$(active_slot_count)"
        return 0
      else
        claim_rc=$?
        if [[ "$claim_rc" == "2" ]]; then
          echo "report-supervisor: Lean slot state is unreadable" >&2
          return 2
        fi
      fi
      if reclaim_stale_lock "$candidate"; then
        continue 2
      else
        reclaim_rc=$?
        if [[ "$reclaim_rc" == "2" ]]; then
          echo "report-supervisor: Lean slot state is unreadable" >&2
          return 2
        fi
      fi
    done
    if (( $(date +%s) >= deadline )); then
      echo "report-supervisor: timed out waiting for a Lean slot" >&2
      return 2
    fi
    sleep 0.1
  done
}

release_lean_slot() {
  [[ -n "$SLOT_DIR" && -n "$SLOT_OWNER_BASE" ]] || return 0
  acquire_lock_guard "$SLOT_DIR" >/dev/null 2>&1 || return 0
  if lock_is_owned_by "$SLOT_DIR" "$SLOT_OWNER_BASE"; then rm -rf -- "$SLOT_DIR"; fi
  release_lock_guard "$SLOT_DIR"
  SLOT_DIR=""
}

write_slot_metadata() {
  local name="$1"
  local value="$2"
  local temporary=""
  [[ -n "$SLOT_DIR" && -n "$SLOT_OWNER_BASE" ]] || return 2
  acquire_lock_guard "$SLOT_DIR" || return 2
  if ! lock_is_owned_by "$SLOT_DIR" "$SLOT_OWNER_BASE"; then
    release_lock_guard "$SLOT_DIR"
    return 2
  fi
  temporary="$SLOT_DIR/.${name}.$$.$RANDOM"
  if ! printf '%s\n' "$value" > "$temporary" || ! mv -f -- "$temporary" "$SLOT_DIR/$name"; then
    rm -f -- "$temporary"
    release_lock_guard "$SLOT_DIR"
    return 2
  fi
  release_lock_guard "$SLOT_DIR"
}

olean_snapshot() {
  local build_root="$PROGRESS_ROOT/.lake/build"
  local list="$TMP_ROOT/olean-files.$$"
  local path mtime
  local count=0
  local newest=0
  if [[ ! -d "$build_root" ]]; then printf '0:0\n'; return 0; fi
  find "$build_root" -type f -name '*.olean' -print0 > "$list" 2>/dev/null || return 1
  while IFS= read -r -d '' path; do
    mtime="$(lock_mtime "$path")" || { rm -f -- "$list"; return 1; }
    count=$((count + 1))
    if [[ "$mtime" -gt "$newest" ]]; then newest="$mtime"; fi
  done < "$list"
  rm -f -- "$list"
  printf '%s:%s\n' "$count" "$newest"
}

producer_log_snapshot() {
  local list="$TMP_ROOT/producer-log-files.$$"
  local path mtime size
  local count=0
  local newest=0
  local bytes=0
  if [[ -z "$PROGRESS_LOG_ROOT" || ! -e "$PROGRESS_LOG_ROOT" ]]; then
    printf '0:0:0\n'
    return 0
  fi
  [[ -d "$PROGRESS_LOG_ROOT" ]] || return 1
  find "$PROGRESS_LOG_ROOT" -type f -print0 > "$list" 2>/dev/null || return 1
  while IFS= read -r -d '' path; do
    mtime="$(lock_mtime "$path")" || { rm -f -- "$list"; return 1; }
    size="$(file_size "$path")" || { rm -f -- "$list"; return 1; }
    count=$((count + 1))
    bytes=$((bytes + size))
    if [[ "$mtime" -gt "$newest" ]]; then newest="$mtime"; fi
  done < "$list"
  rm -f -- "$list"
  printf '%s:%s:%s\n' "$count" "$newest" "$bytes"
}

supervised_processes() {
  {
    if [[ -n "$CHILD_PID" ]]; then collect_process_tree "$CHILD_PID"; fi
    marker_processes
  } | sort -un
}

process_tree_members() {
  if [[ -n "$CHILD_PID" ]]; then collect_process_tree "$CHILD_PID" | sort -un; fi
}

cpu_time_centiseconds() {
  local raw=""
  raw="$(ps -o time= -p "$1" 2>/dev/null | awk '{$1=$1; print; exit}')"
  [[ -n "$raw" ]] || return 1
  awk -v value="$raw" '
    BEGIN {
      days = 0
      if (index(value, "-") > 0) {
        split(value, day_parts, "-")
        days = day_parts[1] + 0
        value = day_parts[2]
      }
      count = split(value, fields, ":")
      seconds = fields[count] + 0
      if (count >= 2) seconds += 60 * (fields[count - 1] + 0)
      if (count >= 3) seconds += 3600 * (fields[count - 2] + 0)
      printf "%.0f\n", 100 * (86400 * days + seconds)
    }
  '
}

cpu_progress_snapshot() {
  local pid ticks members exists_rc
  local total=0
  members="$(process_group_members_for_id "$PROCESS_GROUP_ID")" || return 1
  while IFS= read -r pid; do
    [[ -n "$pid" \
      && "$pid" != "$STDOUT_RELAY_PID" \
      && "$pid" != "$STDERR_RELAY_PID" ]] || continue
    if ! ticks="$(cpu_time_centiseconds "$pid")"; then
      if process_exists "$pid"; then
        return 1
      else
        exists_rc=$?
        [[ "$exists_rc" == "1" ]] && continue
        return 1
      fi
    fi
    [[ "$ticks" =~ ^[0-9]+$ ]] || return 1
    total=$((total + ticks))
  done <<< "$members"
  printf '%s\n' "$total"
}

progress_snapshot() {
  local oleans producer_logs stdout_size stderr_size cpu_time
  oleans="$(olean_snapshot)" || return 1
  producer_logs="$(producer_log_snapshot)" || return 1
  stdout_size="$(file_size "$RUN_STDOUT_CAPTURE")" || return 1
  stderr_size="$(file_size "$RUN_STDERR_CAPTURE")" || return 1
  cpu_time="$(cpu_progress_snapshot)" || return 1
  printf '%s|%s|%s|%s|%s\n' \
    "$cpu_time" "$oleans" "$producer_logs" "$stdout_size" "$stderr_size"
}

initialize_stall_observation() {
  local snapshot=""
  OBSERVATION_WINDOW_STARTED_SECONDS="$(date +%s)"
  LAST_OBSERVATION_CHECK="$OBSERVATION_WINDOW_STARTED_SECONDS"
  if ! snapshot="$(progress_snapshot)"; then
    OBSERVATION_DISABLED=1
    echo "report-supervisor: stall observation disabled because progress state is unavailable" >&2
    return
  fi
  LAST_CPU_SNAPSHOT="${snapshot%%|*}"
  LAST_SIGNAL_SNAPSHOT="${snapshot#*|}"
}

stall_was_observed() {
  local now="$1"
  local current=""
  local current_cpu=""
  local current_signals=""
  [[ "$OBSERVATION_DISABLED" == "0" ]] || return 1
  if ! current="$(progress_snapshot)"; then
    OBSERVATION_DISABLED=1
    echo "report-supervisor: stall observation disabled because progress state became unavailable" >&2
    return 1
  fi
  current_cpu="${current%%|*}"
  current_signals="${current#*|}"
  [[ "$current_cpu" =~ ^[0-9]+$ && "$LAST_CPU_SNAPSHOT" =~ ^[0-9]+$ ]] || {
    OBSERVATION_DISABLED=1
    echo "report-supervisor: stall observation disabled because CPU progress state is invalid" >&2
    return 1
  }
  if [[ "$current_cpu" != "$LAST_CPU_SNAPSHOT" ]]; then
    OBSERVATION_WINDOW_CPU_CHANGED=1
  fi
  if [[ "$current_signals" != "$LAST_SIGNAL_SNAPSHOT" ]]; then
    OBSERVATION_WINDOW_SIGNAL_CHANGED=1
  fi
  LAST_CPU_SNAPSHOT="$current_cpu"
  LAST_SIGNAL_SNAPSHOT="$current_signals"
  if (( now - OBSERVATION_WINDOW_STARTED_SECONDS < STALL_WINDOW_SECONDS )); then
    return 1
  fi
  if [[ "$OBSERVATION_WINDOW_CPU_CHANGED" == "0" \
    && "$OBSERVATION_WINDOW_SIGNAL_CHANGED" == "0" ]]; then
    CONSECUTIVE_STALLED_WINDOWS=$((CONSECUTIVE_STALLED_WINDOWS + 1))
  else
    CONSECUTIVE_STALLED_WINDOWS=0
  fi
  OBSERVATION_WINDOW_STARTED_SECONDS="$now"
  OBSERVATION_WINDOW_CPU_CHANGED=0
  OBSERVATION_WINDOW_SIGNAL_CHANGED=0
  if (( CONSECUTIVE_STALLED_WINDOWS >= STALL_WINDOW_COUNT )); then
    CONSECUTIVE_STALLED_WINDOWS=0
    return 0
  fi
  return 1
}

wait_for_relay() {
  local pid="$1"
  local deadline=$(( $(date +%s) + 2 ))
  local process_rc=0
  while true; do
    if process_exists "$pid"; then
      :
    else
      process_rc=$?
      [[ "$process_rc" == "1" ]] && break
      kill -TERM "$pid" >/dev/null 2>&1 || true
      sleep 0.1
      kill -KILL "$pid" >/dev/null 2>&1 || true
      break
    fi
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
  local claim_rc=0
  local reclaim_rc=0
  while true; do
    if claim_lock "$candidate"; then
      break
    else
      claim_rc=$?
      [[ "$claim_rc" == "2" ]] && return 2
    fi
    if reclaim_stale_lock "$candidate"; then
      :
    else
      reclaim_rc=$?
      [[ "$reclaim_rc" == "2" ]] && return 2
    fi
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
  release_lean_slot
  rm -rf -- "$TMP_ROOT"
  exit "$rc"
}

trap finish EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

if [[ "$LEAN_SLOT" == "1" ]]; then
  acquire_lean_slot
  write_slot_metadata marker "$RUN_MARKER" \
    || { echo "report-supervisor: could not install the Lean producer fence" >&2; exit 2; }
else
  CONCURRENCY_COUNT="$(active_slot_count)"
fi

STARTED_MS="$(now_ms)"
RUN_STDOUT_CAPTURE="$TMP_ROOT/stdout.capture"
RUN_STDERR_CAPTURE="$TMP_ROOT/stderr.capture"
: > "$RUN_STDOUT_CAPTURE"
: > "$RUN_STDERR_CAPTURE"
tee "$RUN_STDOUT_CAPTURE" < "$RUN_STDOUT" &
STDOUT_RELAY_PID=$!
tee "$RUN_STDERR_CAPTURE" < "$RUN_STDERR" >&2 &
STDERR_RELAY_PID=$!
set -m
TMPDIR="$SCRATCH" "$@" 9< "$RUN_MARKER" > "$RUN_STDOUT" 2> "$RUN_STDERR" &
CHILD_PID=$!
PROCESS_GROUP_ID="$CHILD_PID"
set +m
child_start="$(process_start_identity "$CHILD_PID" || true)"
if [[ -z "$child_start" ]]; then child_start=unknown; fi
PROCESS_GROUP_START_IDENTITY="$child_start"
if [[ "$LEAN_SLOT" == "1" ]]; then
  if ! write_slot_metadata group "$PROCESS_GROUP_ID|$CHILD_PID|$child_start"; then
    echo "report-supervisor: infrastructure failure: could not record the Lean producer process group" >&2
    exit 2
  fi
fi
if [[ "$LEAN_SLOT" == "1" ]]; then initialize_stall_observation; fi
BUILD_DEADLINE=0
if (( BUILD_TIMEOUT_SECONDS > 0 )); then
  BUILD_DEADLINE=$(( $(date +%s) + BUILD_TIMEOUT_SECONDS ))
fi
BUILD_TIMED_OUT=0
while true; do
  if process_exists "$CHILD_PID"; then
    :
  else
    process_rc=$?
    if [[ "$process_rc" == "2" ]]; then
      echo "report-supervisor: infrastructure failure: worker process state is unavailable" >&2
      exit 2
    fi
    break
  fi
  sample_process_tree
  now_seconds="$(date +%s)"
  if (( BUILD_DEADLINE > 0 )) && (( now_seconds >= BUILD_DEADLINE )); then
    echo "report-supervisor: build exceeded ${BUILD_TIMEOUT_SECONDS}s wall-clock budget;" \
      "terminating to release the lean slot (#403)" >&2
    BUILD_TIMED_OUT=1
    terminate_process_group "$PROCESS_GROUP_ID" || true
    break
  fi
  if [[ "$LEAN_SLOT" == "1" && "$now_seconds" -ge $((LAST_OBSERVATION_CHECK + OBSERVATION_POLL_SECONDS)) ]]; then
    LAST_OBSERVATION_CHECK="$now_seconds"
    if stall_was_observed "$now_seconds"; then
      echo "report-supervisor: stall observed: no CPU, .olean, producer-log, stdout, or stderr progress across ${STALL_WINDOW_COUNT} consecutive ${STALL_WINDOW_SECONDS}s windows; producer left running" >&2
    fi
  fi
  sleep 0.1
done
set +e
wait "$CHILD_PID"
rc=$?
set -e
if [[ "$BUILD_TIMED_OUT" == "1" ]]; then
  rc=124
fi
exit "$rc"
