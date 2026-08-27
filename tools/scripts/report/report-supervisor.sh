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
RESOURCE_OBSERVATION_LIB="$REPOSITORY_ROOT/tools/scripts/lib/resource-observation-lib.sh"
[[ -r "$RESOURCE_OBSERVATION_LIB" ]] || exit 2
source "$RESOURCE_OBSERVATION_LIB"
if [[ -d /private/tmp ]]; then DEFAULT_HOST_TMP=/private/tmp; else DEFAULT_HOST_TMP=/tmp; fi
STATE_ROOT="${STRATALINT_SUPERVISOR_ROOT:-$DEFAULT_HOST_TMP/stratalint-report-supervisor-${UID:-$(id -u)}}"
RUN_ROOT="$STATE_ROOT/runs"
SLOT_ROOT="$STATE_ROOT/slots"
# 默认槽数 5(2026-08-15 用户裁决;同日先定 3,再定 5)。此前是 1,且全仓没有任何
# 注释/文档/测试记载 1 的案由。
#
# 留档的反对读数,以免下一个人以为这是吞吐优化:实测一次 Lean 构建自身即跑 10+ 个 lean
# 进程、每个约 85% CPU,全机 `top -l 2` 两次采样 idle 均为 0.12%(28 核 / 96 GB)。所以
# 一次构建已把核吃满,加槽不增总吞吐,只把同样的核分成 N 份、每份慢 N 倍。内存不是约束
# (测时 44 GB 空闲,而当时已有一次构建在跑、其总 RSS 11.5 GB)。用户在看过这组读数后
# 先定 3、再定 5,故照办。
#
# 但内存在 5 槽处**可能**变成约束,把算术留在这里:测时 96 GB 中 51 GB 已用、44 GB 空闲,
# 其中含一次构建的 11.5 GB,故无构建时的空闲约 55 GB;5 个并发满构建约 5×11.5 = 57.5 GB,
# 已越过它。**这是外推不是实测**——11.5 GB 是某一时刻的总 RSS 而非峰值,且实际很少五槽同时
# 满载。若出现换页/卡顿,先量 memory_pressure 再谈调整,不要凭感觉回退默认值。
#
# 它确实能改善的是**延迟与失败率**:等槽者的耐心 LOCK_TIMEOUT_SECONDS 默认 900s,而持槽者
# 合法可持有 BUILD_TIMEOUT_SECONDS=7200s,两者差 8 倍,且 acquire_lean_slot 是 mkdir 抢占
# 自旋而非 FIFO——并行 worktree 下先到者会被后到者反复抢先直到超时判红(实测:持槽 24m24s,
# 等槽者 15 分钟阵亡)。槽多了撞上这条的概率随之下降。根因另见 #1910,本改动不假装修了它。
MAX_CONCURRENCY="${STRATALINT_LEAN_MAX_CONCURRENCY:-5}"
[[ "$MAX_CONCURRENCY" =~ ^[1-9][0-9]*$ && "$MAX_CONCURRENCY" -le 64 ]] \
  || { echo "report-supervisor: STRATALINT_LEAN_MAX_CONCURRENCY must be 1..64" >&2; exit 2; }
# 等槽者必须熬得过一个**合法**的持槽者,故此默认值不得小于 BUILD_TIMEOUT_SECONDS。
# 此前是 900s(15 分钟),而持槽者合法可持有 7200s(2 小时),差 8 倍——于是一次正常的长构建
# 就让所有并发等待者判红。2026-08-15 实测:持槽 24m24s,等待中的 `make preflight` 在 15 分钟
# 处以 `timed out waiting for a Lean slot` 判红,判词读上去像等待者自己的问题。
# 多 worktree 并行是本仓常态(第16条),这不是罕见路径。不变量由
# WaiterBudgetOutlastsALegitimateHolder 机器守卫。
#
# 代价(如实记):真死锁的暴露时间因此由 15 分钟变为 2 小时。缓解是 reclaim_stale_lock
# 对死掉的持槽者立即回收,而活着的持槽者本就是合法的。剩下的饥饿(mkdir 抢占自旋而非
# FIFO,先到者可被后到者反复抢先)是 #1910 的另一半,本改动不假装修了它。
LOCK_TIMEOUT_SECONDS="${STRATALINT_LOCK_TIMEOUT_SECONDS:-7200}"
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
CLOCK_SOURCE="${STRATALINT_SUPERVISOR_CLOCK:-}"
if [[ -n "$CLOCK_SOURCE" && ( "$CLOCK_SOURCE" != /* || ! -x "$CLOCK_SOURCE" ) ]]; then
  echo "report-supervisor: STRATALINT_SUPERVISOR_CLOCK must be an absolute executable" >&2
  exit 2
fi

TMP_ROOT=""
CHILD_PID=""
PROCESS_GROUP_ID=""
PROCESS_CANDIDATES_FILE=""
STDOUT_RELAY_PID=""
STDERR_RELAY_PID=""
SLOT_DIR=""
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

mkdir -p "$RUN_ROOT" "$SLOT_ROOT"
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

now_seconds() {
  local value=""
  if [[ -n "$CLOCK_SOURCE" ]]; then
    value="$("$CLOCK_SOURCE")"
  else
    value="$(date +%s)"
  fi
  [[ "$value" =~ ^[0-9]+$ ]] \
    || { echo "report-supervisor: clock source returned a non-integer epoch" >&2; return 2; }
  printf '%s\n' "$value"
}

now_ms() {
  printf '%s000\n' "$(now_seconds)"
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
  (( $(now_seconds) - mtime >= LOCK_INITIALIZATION_GRACE_SECONDS ))
}

process_command() {
  ps -ww -o command= -p "$1" 2>/dev/null | awk '{$1=$1; print; exit}'
}

format_duration() {
  local total_seconds="$1"
  local days=$((total_seconds / 86400))
  local hours=$(((total_seconds % 86400) / 3600))
  local minutes=$(((total_seconds % 3600) / 60))
  local seconds=$((total_seconds % 60))
  if (( days > 0 )); then
    printf '%dd%dh%dm%ds' "$days" "$hours" "$minutes" "$seconds"
  elif (( hours > 0 )); then
    printf '%dh%dm%ds' "$hours" "$minutes" "$seconds"
  elif (( minutes > 0 )); then
    printf '%dm%ds' "$minutes" "$seconds"
  else
    printf '%ds' "$seconds"
  fi
}

report_stale_lock_owner() {
  local slot="$1"
  local pid="$2"
  local expected_start="$3"
  local phase="$4"
  local actual_start=""
  if ! process_exists "$pid"; then
    echo "report-supervisor: $slot recorded holder exited $phase" >&2
    return
  fi
  actual_start="$(process_start_identity "$pid" || true)"
  if [[ -z "$actual_start" ]]; then
    echo "report-supervisor: $slot holder identity unavailable for recorded pid=$pid $phase" >&2
  elif [[ "$actual_start" != "$expected_start" ]]; then
    printf 'report-supervisor: %s recorded holder PID was reused %s; expected_since=%s actual_since=%s\n' \
      "$slot" "$phase" "$expected_start" "$actual_start" >&2
  else
    echo "report-supervisor: $slot holder state changed $phase" >&2
  fi
}

report_lean_slot_holder() {
  local lock="$1"
  local slot="${lock##*/}"
  local owner=""
  local confirmed_owner=""
  local pid=""
  local expected_start=""
  local actual_start=""
  local command=""
  local mtime=""
  local current_time=""
  local held_seconds=""
  local held_for=""

  if [[ ! -d "$lock" ]]; then
    echo "report-supervisor: $slot was released before timeout diagnostics" >&2
    return
  fi
  if [[ -f "$lock/owner" ]]; then
    read -r owner < "$lock/owner" || owner=""
  fi
  if [[ ! "$owner" =~ ^([1-9][0-9]*)\|(.*)$ ]]; then
    echo "report-supervisor: $slot holder identity unavailable: owner record is missing or malformed" >&2
    return
  fi
  pid="${BASH_REMATCH[1]}"
  expected_start="${BASH_REMATCH[2]}"
  if lock_is_stale "$lock"; then
    report_stale_lock_owner "$slot" "$pid" "$expected_start" \
      "before timeout diagnostics"
    return
  fi

  actual_start="$(process_start_identity "$pid" || true)"
  command="$(process_command "$pid" || true)"
  mtime="$(lock_mtime "$lock" || true)"
  if [[ -f "$lock/owner" ]]; then
    read -r confirmed_owner < "$lock/owner" || confirmed_owner=""
  fi
  if [[ "$confirmed_owner" != "$owner" ]]; then
    echo "report-supervisor: $slot holder changed while timeout diagnostics were collected" >&2
    return
  fi
  if lock_is_stale "$lock"; then
    report_stale_lock_owner "$slot" "$pid" "$expected_start" \
      "while timeout diagnostics were collected"
    return
  fi
  if [[ -z "$actual_start" ]]; then
    echo "report-supervisor: $slot holder identity unavailable for recorded pid=$pid while timeout diagnostics were collected" >&2
    return
  fi
  if [[ "$actual_start" != "$expected_start" ]]; then
    echo "report-supervisor: $slot holder changed while timeout diagnostics were collected" >&2
    return
  fi
  if [[ -z "$command" ]]; then
    echo "report-supervisor: $slot holder command unavailable for confirmed pid=$pid" >&2
    return
  fi
  current_time="$(now_seconds)"
  if [[ ! "$mtime" =~ ^[0-9]+$ || "$mtime" -gt "$current_time" ]]; then
    echo "report-supervisor: $slot hold duration unavailable: lock timestamp is invalid" >&2
    return
  fi
  held_seconds=$((current_time - mtime))
  held_for="$(format_duration "$held_seconds")"
  printf 'report-supervisor: %s holder pid=%s since=%s held_for=%s command=%s\n' \
    "$slot" "$pid" "$expected_start" "$held_for" "$command" >&2
}

report_lean_slot_timeout() {
  local index
  echo "report-supervisor: timed out waiting for a Lean slot" >&2
  for ((index = 1; index <= MAX_CONCURRENCY; index++)); do
    report_lean_slot_holder "$SLOT_ROOT/slot-$index.lock"
  done
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
  local deadline=$(( $(now_seconds) + LOCK_TIMEOUT_SECONDS ))
  local identity
  identity="$(owner_identity)" \
    || { echo "report-supervisor: could not identify lock owner process" >&2; return 2; }
  while ! mkdir "$guard" 2>/dev/null; do
    reclaim_lock_without_guard "$guard" || true
    if (( $(now_seconds) >= deadline )); then return 2; fi
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
  local identity
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
  release_lock_guard "$lock"
}

acquire_lean_slot() {
  local index
  local candidate
  local deadline=$(( $(now_seconds) + LOCK_TIMEOUT_SECONDS ))
  while true; do
    for ((index = 1; index <= MAX_CONCURRENCY; index++)); do
      candidate="$SLOT_ROOT/slot-$index.lock"
      if claim_lock "$candidate"; then
        SLOT_DIR="$candidate"
        return 0
      fi
      reclaim_stale_lock "$candidate" || true
    done
    if (( $(now_seconds) >= deadline )); then
      report_lean_slot_timeout
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

sample_supervised_resources() {
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
    rss="$( { ps -o rss= -p "$pid" 2>/dev/null || true; } \
      | awk '{sum += $1} END {print sum + 0}')"
    rss_total=$((rss_total + rss))
    if [[ -d "/proc/$pid/fd" ]]; then
      fd="$( { find "/proc/$pid/fd" -mindepth 1 -maxdepth 1 -print 2>/dev/null || true; } \
        | awk 'END {print NR + 0}')"
    elif command -v lsof >/dev/null 2>&1; then
      fd="$( { lsof -a -p "$pid" -d 0-999999 2>/dev/null || true; } \
        | awk 'NR > 1 {count++} END {print count + 0}')"
    else
      fd=0
    fi
    fd_total=$((fd_total + fd))
  done <<< "$members"
  if [[ "$rss_total" -gt "$RSS_PEAK_KB" ]]; then RSS_PEAK_KB="$rss_total"; fi
  if [[ "$fd_total" -gt "$FD_PEAK" ]]; then FD_PEAK="$fd_total"; fi
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
  local deadline=$(( $(now_seconds) + 2 ))
  local state=""
  while process_exists "$pid"; do
    state="$(ps -o stat= -p "$pid" 2>/dev/null | awk '{$1=$1; print; exit}')"
    if [[ -z "$state" || "$state" == Z* ]]; then break; fi
    if (( $(now_seconds) >= deadline )); then
      kill -TERM "$pid" >/dev/null 2>&1 || true
      sleep 0.1
      kill -KILL "$pid" >/dev/null 2>&1 || true
      break
    fi
    sleep 0.05
  done
  wait "$pid" >/dev/null 2>&1 || true
}

finish() {
  local rc=$?
  trap - EXIT HUP INT TERM
  set +e
  if [[ -n "$PROCESS_GROUP_ID" ]]; then
    sample_supervised_resources
    terminate_process_group "$PROCESS_GROUP_ID"
  fi
  if [[ -n "$CHILD_PID" ]]; then
    wait "$CHILD_PID" >/dev/null 2>&1 || true
  fi
  if [[ -n "$STDOUT_RELAY_PID" ]]; then wait_for_relay "$STDOUT_RELAY_PID"; fi
  if [[ -n "$STDERR_RELAY_PID" ]]; then wait_for_relay "$STDERR_RELAY_PID"; fi
  resource_observe "report-supervisor-$ROLE" "$REPOSITORY_ROOT" "$FD_PEAK" "$RSS_PEAK_KB" || true
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
  BUILD_DEADLINE=$(( $(now_seconds) + BUILD_TIMEOUT_SECONDS ))
fi
BUILD_TIMED_OUT=0
while process_exists "$CHILD_PID"; do
  sample_supervised_resources
  if (( BUILD_DEADLINE > 0 )) && (( $(now_seconds) >= BUILD_DEADLINE )); then
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
