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
LEAN_SLOT_LEASE_SECONDS="${STRATALINT_LEAN_SLOT_LEASE_SECONDS:-1800}"
[[ "$LEAN_SLOT_LEASE_SECONDS" =~ ^[1-9][0-9]*$ \
  && "$LEAN_SLOT_LEASE_SECONDS" -ge 5 \
  && "$LEAN_SLOT_LEASE_SECONDS" -le 86400 ]] \
  || { echo "report-supervisor: STRATALINT_LEAN_SLOT_LEASE_SECONDS must be 5..86400" >&2; exit 2; }
STALL_TIMEOUT_SECONDS="${STRATALINT_REPORT_STALL_TIMEOUT_SECONDS:-1200}"
[[ "$STALL_TIMEOUT_SECONDS" =~ ^[1-9][0-9]*$ && "$STALL_TIMEOUT_SECONDS" -le 86400 ]] \
  || { echo "report-supervisor: STRATALINT_REPORT_STALL_TIMEOUT_SECONDS must be 1..86400" >&2; exit 2; }
WATCHDOG_POLL_SECONDS="${STRATALINT_REPORT_WATCHDOG_POLL_SECONDS:-5}"
[[ "$WATCHDOG_POLL_SECONDS" =~ ^[1-9][0-9]*$ && "$WATCHDOG_POLL_SECONDS" -le 300 ]] \
  || { echo "report-supervisor: STRATALINT_REPORT_WATCHDOG_POLL_SECONDS must be 1..300" >&2; exit 2; }
PROGRESS_ROOT="${STRATALINT_LEAN_PROGRESS_ROOT:-$PWD}"
[[ "$LEAN_SLOT" == "0" || ( "$PROGRESS_ROOT" == /* && -d "$PROGRESS_ROOT" ) ]] \
  || { echo "report-supervisor: STRATALINT_LEAN_PROGRESS_ROOT must be an absolute directory" >&2; exit 2; }
PROGRESS_LOG_ROOT="${STRATALINT_LEAN_PROGRESS_LOG_ROOT:-}"
[[ "$LEAN_SLOT" == "0" || -z "$PROGRESS_LOG_ROOT" || "$PROGRESS_LOG_ROOT" == /* ]] \
  || { echo "report-supervisor: STRATALINT_LEAN_PROGRESS_LOG_ROOT must be absolute when set" >&2; exit 2; }
LOCK_INITIALIZATION_GRACE_SECONDS=5
LEASE_DURATION_MS=$((LEAN_SLOT_LEASE_SECONDS * 1000))
LEASE_RENEW_INTERVAL_MS=$((LEASE_DURATION_MS / 3))
if [[ "$LEASE_RENEW_INTERVAL_MS" -lt 100 ]]; then LEASE_RENEW_INTERVAL_MS=100; fi
LEASE_SELF_FENCE_MARGIN_MS=$((LEASE_DURATION_MS / 5))
if [[ "$LEASE_SELF_FENCE_MARGIN_MS" -gt 1000 ]]; then LEASE_SELF_FENCE_MARGIN_MS=1000; fi

TMP_ROOT=""
CHILD_PID=""
PROCESS_GROUP_ID=""
STDOUT_RELAY_PID=""
STDERR_RELAY_PID=""
SLOT_DIR=""
SLOT_OWNER_BASE=""
METRICS_LOCK_DIR=""
CONCURRENCY_COUNT=0
FD_PEAK=0
RSS_PEAK_KB=0
STARTED_MS=0
LAST_LEASE_RENEWED_MS=0
LAST_PROGRESS_SECONDS=0
LAST_WATCHDOG_CHECK=0
LAST_PROGRESS_SNAPSHOT=""
WATCHDOG_DISABLED=0
WATCHDOG_FAILURE=0
CLAIMED_OWNER_BASE=""
ACTIVE_GUARD_PATH=""
ACTIVE_GUARD_TOKEN=""
RENEWAL_WARNING_EMITTED=0

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

process_start_identity() {
  ps -o lstart= -p "$1" 2>/dev/null | awk '{$1=$1; print; exit}'
}

owner_base_identity() {
  local start
  start="$(process_start_identity "$$")"
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

lease_is_expired() {
  local timestamp="$1"
  local now
  now="$(now_ms)"
  [[ "$timestamp" =~ ^[0-9]+$ && "$now" =~ ^[0-9]+$ ]] || return 1
  if [[ "$timestamp" -lt 1000000000000 ]]; then timestamp=$((timestamp * 1000)); fi
  (( timestamp <= now && now - timestamp >= LEASE_DURATION_MS ))
}

lock_is_stale() {
  local lock="$1"
  local owner=""
  local pid=""
  local expected_start=""
  local actual_start=""
  local lease_timestamp=""
  local mtime=""
  if [[ -f "$lock/owner" ]]; then
    read -r owner < "$lock/owner" || return 1
  fi
  if [[ "$owner" =~ ^([1-9][0-9]*)\|([^|]+)\|([0-9]+)$ ]]; then
    pid="${BASH_REMATCH[1]}"
    expected_start="${BASH_REMATCH[2]}"
    lease_timestamp="${BASH_REMATCH[3]}"
    if ! process_exists "$pid"; then
      fence_stale_slot "$lock" || return 1
      return 0
    fi
    if [[ "$expected_start" == "unknown" ]]; then
      return 1
    fi
    actual_start="$(process_start_identity "$pid")"
    [[ -n "$actual_start" ]] || return 1
    if [[ "$actual_start" != "$expected_start" ]]; then
      fence_stale_slot "$lock" || return 1
      return 0
    fi
    lease_is_expired "$lease_timestamp" || return 1
    fence_stale_slot "$lock"
    return
  fi
  if [[ "$owner" =~ ^([1-9][0-9]*)\|([^|]+)$ ]]; then
    pid="${BASH_REMATCH[1]}"
    expected_start="${BASH_REMATCH[2]}"
    process_exists "$pid" || return 0
    actual_start="$(process_start_identity "$pid")"
    [[ -n "$actual_start" ]] || return 1
    [[ "$actual_start" == "$expected_start" ]] || return 0
    return 1
  fi
  if [[ "$owner" =~ ^[1-9][0-9]*$ ]]; then
    process_exists "$owner" || return 0
    return 1
  fi
  [[ ! -e "$lock/owner" ]] || return 1
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
  local wait_for_guard="${2:-1}"
  local guard="${lock}.reclaim-guard"
  local deadline=$(( $(date +%s) + LOCK_TIMEOUT_SECONDS ))
  local identity
  identity="$(owner_base_identity)" \
    || { echo "report-supervisor: could not identify lock owner process" >&2; return 2; }
  while ! mkdir "$guard" 2>/dev/null; do
    [[ "$wait_for_guard" == "1" ]] || return 1
    reclaim_lock_without_guard "$guard" || true
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
  acquire_lock_guard "$lock" || return 1
  reclaim_lock_without_guard "$lock"
  local rc=$?
  release_lock_guard "$lock"
  return "$rc"
}

claim_lock() {
  local lock="$1"
  local identity
  identity="$(owner_base_identity)" \
    || { echo "report-supervisor: could not identify lock owner process" >&2; return 2; }
  acquire_lock_guard "$lock" || return 1
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
  local deadline=$(( $(date +%s) + LOCK_TIMEOUT_SECONDS ))
  while true; do
    for ((index = 1; index <= MAX_CONCURRENCY; index++)); do
      candidate="$SLOT_ROOT/slot-$index.lock"
      if claim_lock "$candidate"; then
        SLOT_DIR="$candidate"
        SLOT_OWNER_BASE="$CLAIMED_OWNER_BASE"
        LAST_LEASE_RENEWED_MS="$(now_ms)"
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

renew_lean_slot() {
  [[ -n "$SLOT_DIR" && -n "$SLOT_OWNER_BASE" ]] || return 2
  acquire_lock_guard "$SLOT_DIR" 0 || return 1
  if ! lock_is_owned_by "$SLOT_DIR" "$SLOT_OWNER_BASE"; then
    release_lock_guard "$SLOT_DIR"
    return 2
  fi
  if ! write_lock_owner "$SLOT_DIR" "$SLOT_OWNER_BASE"; then
    release_lock_guard "$SLOT_DIR"
    return 1
  fi
  release_lock_guard "$SLOT_DIR"
  LAST_LEASE_RENEWED_MS="$(now_ms)"
  RENEWAL_WARNING_EMITTED=0
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
  local pid ticks
  local total=0
  while IFS= read -r pid; do
    [[ -n "$pid" \
      && "$pid" != "$STDOUT_RELAY_PID" \
      && "$pid" != "$STDERR_RELAY_PID" ]] || continue
    if ! ticks="$(cpu_time_centiseconds "$pid")"; then
      process_exists "$pid" || continue
      return 1
    fi
    [[ "$ticks" =~ ^[0-9]+$ ]] || return 1
    total=$((total + ticks))
  done < <(process_tree_members)
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

initialize_watchdog() {
  LAST_PROGRESS_SECONDS="$(date +%s)"
  LAST_WATCHDOG_CHECK="$LAST_PROGRESS_SECONDS"
  if ! LAST_PROGRESS_SNAPSHOT="$(progress_snapshot)"; then
    WATCHDOG_DISABLED=1
    echo "report-supervisor: watchdog disabled because progress state is unavailable; refusing to guess that a live build is stalled" >&2
  fi
}

watchdog_has_stalled() {
  local now="$1"
  local current=""
  [[ "$WATCHDOG_DISABLED" == "0" ]] || return 1
  if ! current="$(progress_snapshot)"; then
    WATCHDOG_DISABLED=1
    echo "report-supervisor: watchdog disabled because progress state became unavailable; refusing to guess that a live build is stalled" >&2
    return 1
  fi
  if [[ "$current" != "$LAST_PROGRESS_SNAPSHOT" ]]; then
    LAST_PROGRESS_SNAPSHOT="$current"
    LAST_PROGRESS_SECONDS="$now"
    return 1
  fi
  (( now - LAST_PROGRESS_SECONDS >= STALL_TIMEOUT_SECONDS ))
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
if [[ "$LEAN_SLOT" == "1" ]]; then
  child_start="$(process_start_identity "$CHILD_PID" || true)"
  if [[ -z "$child_start" ]]; then child_start=unknown; fi
  if ! write_slot_metadata group "$PROCESS_GROUP_ID|$CHILD_PID|$child_start"; then
    echo "report-supervisor: infrastructure failure: could not record the Lean producer process group" >&2
    WATCHDOG_FAILURE=1
    terminate_process_group "$PROCESS_GROUP_ID" || true
  fi
fi
if [[ "$LEAN_SLOT" == "1" ]]; then initialize_watchdog; fi
while process_exists "$CHILD_PID"; do
  now_milliseconds="$(now_ms)"
  if [[ "$LEAN_SLOT" == "1" && "$now_milliseconds" -ge $((LAST_LEASE_RENEWED_MS + LEASE_RENEW_INTERVAL_MS)) ]]; then
    renewal_rc=0
    renew_lean_slot || renewal_rc=$?
    if [[ "$renewal_rc" == "2" ]]; then
      echo "report-supervisor: infrastructure failure: Lean slot ownership was lost while the producer was running" >&2
      WATCHDOG_FAILURE=1
      terminate_process_group "$PROCESS_GROUP_ID" || true
      break
    elif [[ "$renewal_rc" != "0" ]]; then
      if [[ "$RENEWAL_WARNING_EMITTED" == "0" ]]; then
        echo "report-supervisor: transient Lean slot renewal failure; retrying inside the current lease window" >&2
        RENEWAL_WARNING_EMITTED=1
      fi
      if [[ "$now_milliseconds" -ge $((LAST_LEASE_RENEWED_MS + LEASE_DURATION_MS - LEASE_SELF_FENCE_MARGIN_MS)) ]]; then
        echo "report-supervisor: infrastructure failure: Lean slot could not be renewed before its safety margin" >&2
        WATCHDOG_FAILURE=1
        terminate_process_group "$PROCESS_GROUP_ID" || true
        break
      fi
    fi
  fi
  sample_process_tree
  now_seconds="$(date +%s)"
  if [[ "$LEAN_SLOT" == "1" && "$now_seconds" -ge $((LAST_WATCHDOG_CHECK + WATCHDOG_POLL_SECONDS)) ]]; then
    LAST_WATCHDOG_CHECK="$now_seconds"
    if watchdog_has_stalled "$now_seconds"; then
      echo "report-supervisor: infrastructure failure: no Lean progress for ${STALL_TIMEOUT_SECONDS}s; terminating producer process group ${PROCESS_GROUP_ID}" >&2
      WATCHDOG_FAILURE=1
      terminate_process_group "$PROCESS_GROUP_ID" || true
      break
    fi
  fi
  sleep 0.1
done
set +e
wait "$CHILD_PID"
rc=$?
set -e
if [[ "$WATCHDOG_FAILURE" == "1" ]]; then rc=2; fi
exit "$rc"
