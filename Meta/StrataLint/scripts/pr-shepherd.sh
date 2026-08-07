#!/usr/bin/env bash
# pr-shepherd —— PR 一门器(一器一门,第Ⅵ节·器之四律①)
#
# 职责:开 PR 到 dev 并挂 auto-merge;轮询在飞 PR。BEHIND 且最新 admission
# 仅因 dev 前进导致派生物过期时,在持久 worktree 合并并走 canonical 重算链;
# 其余 BEHIND 仍由本地 gh 身份 update-branch。CONFLICTING 由本地冲突集分类。
#
# 用法:
#   pr-shepherd.sh open <head-branch> <title> [body-file]   开 PR + 挂 auto-merge
#   pr-shepherd.sh start [interval] [max_cycles]            后台启动并等待 ready
#   pr-shepherd.sh status                                   单行报告 alive/stalled/dead
#   pr-shepherd.sh watch [interval] [max_cycles]            轮询(默认 60s × 360)
#   pr-shepherd.sh sweep                                    单轮扫描(供人工/调试)
#
# 判定只看机器字段(mergeable/mergeStateStatus/autoMergeRequest),不看输出散文。
set -euo pipefail
LOADED_SCRIPT_PATH="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)/${BASH_SOURCE[0]##*/}"
SCRIPT_PATH="${PR_SHEPHERD_CANONICAL_SCRIPT:-$LOADED_SCRIPT_PATH}"
ROOT="${PR_SHEPHERD_ROOT:-$(cd "$(dirname "$SCRIPT_PATH")/../../.." && pwd -P)}"
REMOTE="${PR_SHEPHERD_REMOTE:-origin}"
REPO="${PR_SHEPHERD_REPO:-the-omega-institute/trureturing}"
LOG="${PR_SHEPHERD_LOG:-$HOME/.pr-shepherd.log}"
PIDFILE="${PR_SHEPHERD_PID:-$HOME/.pr-shepherd.pid}"
PIDFILE_PARENT="$(cd "$(dirname "$PIDFILE")" 2>/dev/null && pwd -P)" \
  || { printf 'pr-shepherd: state directory is unavailable: %s\n' "$(dirname "$PIDFILE")" >&2; exit 1; }
PIDFILE="$PIDFILE_PARENT/${PIDFILE##*/}"
STATE_DIR="${PR_SHEPHERD_STATE:-$HOME/.pr-shepherd-state}"
CACHE_ROOT="${PR_SHEPHERD_CACHE:-$HOME/.cache/trureturing-shepherd}"
DRYRUN="${SHEPHERD_DRYRUN:-0}"
DERIVED_LEASE_TTL="${PR_SHEPHERD_LEASE_TTL_SECONDS:-14400}"
API_TIMEOUT_SECONDS="${PR_SHEPHERD_API_TIMEOUT_SECONDS:-120}"
GIT_TIMEOUT_SECONDS="${PR_SHEPHERD_GIT_TIMEOUT_SECONDS:-300}"
BUILD_TIMEOUT_SECONDS="${PR_SHEPHERD_BUILD_TIMEOUT_SECONDS:-1800}"
SWEEP_TIMEOUT_SECONDS="${PR_SHEPHERD_SWEEP_TIMEOUT_SECONDS:-7200}"
KILL_GRACE_SECONDS="${PR_SHEPHERD_KILL_GRACE_SECONDS:-15}"
FAILURE_BACKOFF_BASE_SECONDS="${PR_SHEPHERD_FAILURE_BACKOFF_BASE_SECONDS:-120}"
FAILURE_MAX_CLASS_ATTEMPTS=3
FAILURE_MAX_TOTAL_ATTEMPTS=5
INFRA_BACKOFF_MAX_EXPONENT=3
WAKE_BACKOFF_BASE_SECONDS="${PR_SHEPHERD_WAKE_BACKOFF_BASE_SECONDS:-120}"
WAKE_MAX_ATTEMPTS=3
WAKE_SLEEP_SECONDS="${PR_SHEPHERD_WAKE_SLEEP_SECONDS:-3}"
WAKE_REOPEN_RETRY_SLEEP_SECONDS="${PR_SHEPHERD_WAKE_REOPEN_RETRY_SLEEP_SECONDS:-5}"
DERIVED_LEASE_TOKEN=""
DERIVED_LEASE_PR=""
DERIVED_LEASE_ACQUIRED_AT=""
DERIVED_LEASE_OBSERVED_TOKEN=""
FROZEN_LEDGER_CONFLICT=0
FROZEN_LEDGER_PATH="Meta/StrataLint/Golden/Frozen/events.jsonl"
TRURETURING_ROOT_PATH="Trureturing.lean"
COMMIT_SUBJECT="recompute derivations after dev advance (auto, pr-shepherd)"
ORIGINAL_HOME="${HOME:-/tmp}"
WATCH_LOADED_BLOB="${PR_SHEPHERD_WATCH_LOADED_BLOB:-}"
WATCH_PREVIOUS_SCRIPT="${PR_SHEPHERD_WATCH_PREVIOUS_SCRIPT:-}"
WATCH_PROCESS_START="${PR_SHEPHERD_WATCH_PROCESS_START:-}"
WATCH_OWNS_LEASE=0
WATCH_LOCK_CANDIDATE=""
WATCH_RECLAIM_REPOSITORY=""
WATCH_RECLAIM_REF=""
WATCH_RECLAIM_OID=""
WATCH_STATE_OWNER_PID="${PR_SHEPHERD_WATCH_OWNER_PID:-}"
WATCH_STATE_OWNER_START="${PR_SHEPHERD_WATCH_OWNER_START:-}"
WATCH_STATE_INTERVAL="${PR_SHEPHERD_WATCH_INTERVAL:-}"
WATCH_STATE_MAX="${PR_SHEPHERD_WATCH_MAX_CYCLES:-}"
WATCH_STATE_PHASE=""
WATCH_STATE_CURRENT_PR=""
WATCH_STATE_CURRENT_STEP=""
WATCH_STATE_STEP_STARTED_AT=""
WATCH_STATE_STEP_DEADLINE_AT=""
WATCH_STATE_LAST_PROGRESS_AT=""
WATCH_STATE_LAST_OUTCOME=""
WATCH_STATE_CYCLE=""
WATCH_STATE_TERMINAL_EXIT=""
WATCH_SLEEP_PID=""
ACTIVE_BOUNDED_PID=""
ACTIVE_SWEEP_LEASE_RECEIPT=""
TIMEOUT_COMMAND=""
LAST_BOUNDED_RESULT=""
LAST_BOUNDED_EXIT=""
LAST_FAILURE_CLASS=""
LAST_FAILURE_EXIT=""
LAST_FAILURE_DISPOSITION="poison"
CURRENT_PR="none"
ACTIVE_BRANCH_LOCK=""

configuration_error() {
  printf 'pr-shepherd: CONFIG_INVALID field=%s value=%s\n' "$1" "$2" >&2
  return 2
}
validate_positive_config() {
  local name="$1" value="$2"
  [[ "$value" =~ ^[1-9][0-9]*$ ]] || configuration_error "$name" "$value"
}
resolve_timeout_command() {
  local configured="${PR_SHEPHERD_TIMEOUT_BIN:-}" candidate="" resolved=""
  if [[ -n "$configured" ]]; then
    case "${configured##*/}" in timeout|gtimeout) ;; *) configuration_error PR_SHEPHERD_TIMEOUT_BIN "$configured"; return 2 ;; esac
    resolved="$(command -v "$configured" 2>/dev/null || true)"
    [[ -n "$resolved" && -x "$resolved" ]] \
      || { configuration_error PR_SHEPHERD_TIMEOUT_BIN "$configured"; return 2; }
    TIMEOUT_COMMAND="$resolved"
    return 0
  fi
  for candidate in timeout gtimeout /opt/homebrew/bin/timeout /opt/homebrew/bin/gtimeout; do
    resolved="$(command -v "$candidate" 2>/dev/null || true)"
    if [[ -n "$resolved" && -x "$resolved" ]]; then
      TIMEOUT_COMMAND="$resolved"
      return 0
    fi
  done
  configuration_error PR_SHEPHERD_TIMEOUT_BIN unavailable
}
validate_configuration() {
  validate_positive_config PR_SHEPHERD_API_TIMEOUT_SECONDS "$API_TIMEOUT_SECONDS" || return 2
  validate_positive_config PR_SHEPHERD_GIT_TIMEOUT_SECONDS "$GIT_TIMEOUT_SECONDS" || return 2
  validate_positive_config PR_SHEPHERD_BUILD_TIMEOUT_SECONDS "$BUILD_TIMEOUT_SECONDS" || return 2
  validate_positive_config PR_SHEPHERD_SWEEP_TIMEOUT_SECONDS "$SWEEP_TIMEOUT_SECONDS" || return 2
  validate_positive_config PR_SHEPHERD_KILL_GRACE_SECONDS "$KILL_GRACE_SECONDS" || return 2
  validate_positive_config PR_SHEPHERD_FAILURE_BACKOFF_BASE_SECONDS "$FAILURE_BACKOFF_BASE_SECONDS" || return 2
  if [[ "$SWEEP_TIMEOUT_SECONDS" -le $((KILL_GRACE_SECONDS + 1)) ]]; then
    configuration_error PR_SHEPHERD_SWEEP_TIMEOUT_SECONDS "$SWEEP_TIMEOUT_SECONDS"
    return 2
  fi
  resolve_timeout_command
}

run_bounded() {
  local kind="$1" step="$2" configured_timeout="$3"
  shift 3
  local now deadline child_deadline timeout_seconds completion rc completed_exit bounded_pid
  local parent_step="${PR_SHEPHERD_BOUND_STEP:-}"
  local parent_started_at="${PR_SHEPHERD_BOUND_STARTED_AT:-0}"
  local parent_deadline_at="${PR_SHEPHERD_DEADLINE_AT:-0}"
  now="$(date '+%s')"
  [[ "$now" =~ ^[0-9]+$ ]] \
    || { LAST_BOUNDED_RESULT=exit; LAST_BOUNDED_EXIT=70; return 70; }
  deadline=$((now + configured_timeout))
  if [[ "${PR_SHEPHERD_DEADLINE_AT:-}" =~ ^[0-9]+$ \
      && "$PR_SHEPHERD_DEADLINE_AT" -lt "$deadline" ]]; then
    deadline="$PR_SHEPHERD_DEADLINE_AT"
  fi
  timeout_seconds=$((deadline - now))
  if [[ "$timeout_seconds" -le 0 ]]; then
    LAST_BOUNDED_RESULT=timeout
    LAST_BOUNDED_EXIT=124
    log "deadline_kind=$kind step=$step timeout_seconds=0 result=timeout deadline_at=$deadline exit_code=124"
    return 124
  fi
  child_deadline="$deadline"
  if [[ "$kind" == sweep && "$step" == sweep ]]; then
    child_deadline=$((deadline - KILL_GRACE_SECONDS - 1))
  fi
  if declare -F watch_step_started >/dev/null; then
    watch_step_started "$step" "$deadline" || true
  fi
  completion="$(mktemp "${TMPDIR:-/tmp}/pr-shepherd-completion.XXXXXXXX")"
  rm -f "$completion"
  set +e
  "$TIMEOUT_COMMAND" --signal=TERM --kill-after="${KILL_GRACE_SECONDS}s" \
    "${timeout_seconds}s" /bin/bash -c '
      completion="$1"; deadline="$2"; child_deadline="$3"; started_at="$4"
      kind="$5"; step="$6"; timeout_seconds="$7"; current_pr="$8"
      shift 8
      export PR_SHEPHERD_DEADLINE_AT="$child_deadline"
      export PR_SHEPHERD_BOUND_KIND="$kind"
      export PR_SHEPHERD_BOUND_STEP="$step"
      export PR_SHEPHERD_BOUND_STARTED_AT="$started_at"
      export PR_SHEPHERD_BOUND_TIMEOUT_SECONDS="$timeout_seconds"
      export PR_SHEPHERD_CURRENT_PR="$current_pr"
      timed_out=0
      trap "timed_out=1" TERM
      "$@"
      rc=$?
      [[ "$timed_out" == 0 ]] || exit 143
      temporary="$completion.next.$$"
      printf "%s\n" "$rc" > "$temporary" && mv "$temporary" "$completion"
      exit "$rc"
    ' pr-shepherd-bounded "$completion" "$deadline" "$child_deadline" "$now" \
      "$kind" "$step" "$timeout_seconds" "$CURRENT_PR" "$@" &
  bounded_pid=$!
  ACTIVE_BOUNDED_PID="$bounded_pid"
  wait "$bounded_pid"
  rc=$?
  ACTIVE_BOUNDED_PID=""
  set -e
  if [[ -f "$completion" ]]; then
    completed_exit="$(<"$completion")"
    rm -f "$completion"
    if [[ "$completed_exit" =~ ^(0|[1-9][0-9]{0,2})$ ]]; then
      LAST_BOUNDED_RESULT="$([[ "$completed_exit" == 0 ]] && printf success || printf exit)"
      LAST_BOUNDED_EXIT="$completed_exit"
      if [[ "$completed_exit" != 0 ]]; then
        log "deadline_kind=$kind step=$step timeout_seconds=$timeout_seconds result=exit deadline_at=$deadline exit_code=$completed_exit"
      fi
      if declare -F watch_step_finished >/dev/null; then
        watch_step_finished "$step" "$LAST_BOUNDED_RESULT" \
          "$parent_step" "$parent_started_at" "$parent_deadline_at" || true
      fi
      return "$completed_exit"
    fi
    LAST_BOUNDED_RESULT=exit
    LAST_BOUNDED_EXIT=70
    log "deadline_kind=$kind step=$step timeout_seconds=$timeout_seconds result=exit deadline_at=$deadline exit_code=70 completion=invalid"
    return 70
  fi
  rm -f "$completion" "$completion".next.* 2>/dev/null || true
  LAST_BOUNDED_RESULT=timeout
  LAST_BOUNDED_EXIT=124
  log "deadline_kind=$kind step=$step timeout_seconds=$timeout_seconds result=timeout deadline_at=$deadline exit_code=$rc"
  if declare -F watch_step_finished >/dev/null; then
    watch_step_finished "$step" timeout \
      "$parent_step" "$parent_started_at" "$parent_deadline_at" || true
  fi
  return 124
}
run_bounded_capture() {
  local variable="$1" kind="$2" step="$3" timeout="$4" output rc=0
  shift 4
  output="$(mktemp "${TMPDIR:-/tmp}/pr-shepherd-output.XXXXXXXX")"
  if run_bounded "$kind" "$step" "$timeout" "$@" > "$output"; then rc=0; else rc=$?; fi
  printf -v "$variable" '%s' "$(<"$output")"
  rm -f "$output"
  return "$rc"
}
GH() {
  local step="$1"
  shift
  run_bounded api "$step" "$API_TIMEOUT_SECONDS" \
    env LEAN4_GUARDRAILS_BYPASS=1 gh "$@"
}
GH_CAPTURE() {
  local variable="$1" step="$2"
  shift 2
  run_bounded_capture "$variable" api "$step" "$API_TIMEOUT_SECONDS" \
    env LEAN4_GUARDRAILS_BYPASS=1 gh "$@"
}
GH_AS_APP() {
  local step="$1" token=""
  shift
  if command -v gh-app >/dev/null 2>&1 \
      && run_bounded_capture token api gh-app-token "$API_TIMEOUT_SECONDS" gh-app token --auto \
      && [[ -n "$token" ]]; then
    run_bounded api "$step" "$API_TIMEOUT_SECONDS" \
      env GH_TOKEN="$token" LEAN4_GUARDRAILS_BYPASS=1 gh "$@"
  else
    GH "$step" "$@"
  fi
}
GH_AS_APP_CAPTURE() {
  local variable="$1" step="$2" token=""
  shift 2
  if command -v gh-app >/dev/null 2>&1 \
      && run_bounded_capture token api gh-app-token "$API_TIMEOUT_SECONDS" gh-app token --auto \
      && [[ -n "$token" ]]; then
    run_bounded_capture "$variable" api "$step" "$API_TIMEOUT_SECONDS" \
      env GH_TOKEN="$token" LEAN4_GUARDRAILS_BYPASS=1 gh "$@"
  else
    GH_CAPTURE "$variable" "$step" "$@"
  fi
}
log() { printf '%s %s\n' "$(date '+%F %T')" "$*" | tee -a "$LOG" >&2; }
SHEPHERD_MODULE_NAMES=(pr-shepherd-actions.sh pr-shepherd-ledger.sh pr-shepherd-lease.sh)
SHEPHERD_MODULE_DIR="$(cd "$(dirname "$LOADED_SCRIPT_PATH")" && pwd -P)/shepherd"
compute_shepherd_identity() {
  local entrypoint="$1" module_directory="$2" name blob material=""
  blob="$(git hash-object "$entrypoint" 2>/dev/null)" || return 1
  [[ "$blob" =~ ^[0-9a-f]{40}$ ]] || return 1
  material="pr-shepherd.sh $blob"
  for name in "${SHEPHERD_MODULE_NAMES[@]}"; do
    blob="$(git hash-object "$module_directory/$name" 2>/dev/null)" || return 1
    [[ "$blob" =~ ^[0-9a-f]{40}$ ]] || return 1
    material+=$'\n'"shepherd/$name $blob"
  done
  printf '%s\n' "$material" | git hash-object --stdin
}
if [[ "${1:-}" != watch || -n "$WATCH_LOADED_BLOB" ]]; then
  source "$SHEPHERD_MODULE_DIR/pr-shepherd-actions.sh"
  source "$SHEPHERD_MODULE_DIR/pr-shepherd-ledger.sh"
  source "$SHEPHERD_MODULE_DIR/pr-shepherd-lease.sh"
fi
watch_process_start() {
  LC_ALL=C ps -p "$1" -o lstart= 2>/dev/null \
    | sed 's/^[[:space:]]*//;s/[[:space:]]*$//'
}
# 0=live owner, 1=recorded owner is provably gone, 2=identity cannot be verified.
watch_lease_owner_status() {
  local owner_file="${1:-$PIDFILE.lock}" line pid process_start canonical_script
  local actual_start="" process_status
  local -a lines=()
  WATCH_OWNER_PID=""
  WATCH_OWNER_PROCESS_START=""
  WATCH_OWNER_CANONICAL_SCRIPT=""
  [[ -f "$owner_file" && -r "$owner_file" ]] || return 2
  while IFS= read -r line || [[ -n "$line" ]]; do
    lines+=("$line")
  done < "$owner_file"
  [[ "${#lines[@]}" -eq 4 \
      && "${lines[0]}" == "schema=pr-watch-owner-v1" \
      && "${lines[1]}" =~ ^pid=([1-9][0-9]*)$ \
      && "${lines[2]}" == process_start=* \
      && "${lines[3]}" == canonical_script=/* ]] || return 2
  pid="${BASH_REMATCH[1]}"
  process_start="${lines[2]#process_start=}"
  canonical_script="${lines[3]#canonical_script=}"
  [[ -n "$process_start" && -n "$canonical_script" ]] || return 2
  WATCH_OWNER_PID="$pid"
  WATCH_OWNER_PROCESS_START="$process_start"
  WATCH_OWNER_CANONICAL_SCRIPT="$canonical_script"
  if actual_start="$(watch_process_start "$pid")"; then
    process_status=0
  else
    process_status=$?
    actual_start=""
  fi
  if kill -0 "$pid" 2>/dev/null; then
    [[ "$process_status" == "0" && "$actual_start" == "$process_start" ]] \
      && return 0
    return 2
  fi
  if [[ "$process_status" == "1" && -z "$actual_start" ]]; then
    return 1
  fi
  if [[ "$process_status" == "0" && -n "$actual_start" \
      && "$actual_start" != "$process_start" ]]; then
    return 1
  fi
  return 2
}
write_watch_owner() {
  local target="$1"
  (set -o noclobber; {
      printf 'schema=pr-watch-owner-v1\n'
      printf 'pid=%s\n' "$$"
      printf 'process_start=%s\n' "$WATCH_PROCESS_START"
      printf 'canonical_script=%s\n' "$SCRIPT_PATH"
    } > "$target") 2>/dev/null
}
clear_watch_reclaim() {
  local rc=0
  if [[ -n "$WATCH_RECLAIM_REF" && -n "$WATCH_RECLAIM_OID" ]]; then
    if ! git -C "$WATCH_RECLAIM_REPOSITORY" update-ref -d \
        "$WATCH_RECLAIM_REF" "$WATCH_RECLAIM_OID" 2>/dev/null; then
      log "WATCH lease unavailable: reclaim claim release failed"
      rc=1
    fi
  fi
  WATCH_RECLAIM_REPOSITORY=""
  WATCH_RECLAIM_REF=""
  WATCH_RECLAIM_OID=""
  return "$rc"
}
acquire_watch_reclaim_claim() {
  local candidate="$1" repository candidate_oid observed_oid observed_status attempt rc observed
  local zero=0000000000000000000000000000000000000000
  repository="$PIDFILE.reclaim.git"
  if ! git init --bare -q "$repository" 2>/dev/null; then
    log "WATCH lease unavailable: reclaim repository cannot be initialized"; return 1
  fi
  [[ "$(git -C "$repository" rev-parse --is-bare-repository 2>/dev/null)" == "true" ]] \
    || { log "WATCH lease unavailable: reclaim repository is invalid"; return 1; }
  candidate_oid="$(git -C "$repository" hash-object -w "$candidate" 2>/dev/null)" \
    || candidate_oid=""
  [[ "$candidate_oid" =~ ^[0-9a-f]{40}$ ]] \
    || { log "WATCH lease unavailable: reclaim identity cannot be stored"; return 1; }
  WATCH_RECLAIM_REF="refs/trureturing/pr-watch-reclaim"
  for attempt in 1 2 3; do
    if observed_oid="$(git -C "$repository" rev-parse --verify --quiet \
        "$WATCH_RECLAIM_REF" 2>/dev/null)"; then
      observed="$candidate.observed"
      if ! git -C "$repository" cat-file blob "$observed_oid" \
          > "$observed" 2>/dev/null; then
        rm -f "$observed"
        log "WATCH lease unavailable: reclaim identity is unverifiable"
        return 1
      fi
      watch_lease_owner_status "$observed" && observed_status=0 || observed_status=$?
      rm -f "$observed"
      case "$observed_status" in
        0) log "WATCH lease unavailable: ownership reclamation already in progress"; return 1 ;;
        2) log "WATCH lease unavailable: reclaim identity is unverifiable"; return 1 ;;
      esac
    else
      rc=$?
      [[ "$rc" == "1" ]] \
        || { log "WATCH lease unavailable: reclaim claim cannot be read"; return 1; }
      observed_oid="$zero"
    fi
    if git -C "$repository" update-ref "$WATCH_RECLAIM_REF" \
        "$candidate_oid" "$observed_oid" 2>/dev/null; then
      WATCH_RECLAIM_REPOSITORY="$repository"
      WATCH_RECLAIM_OID="$candidate_oid"
      return 0
    fi
  done
  log "WATCH lease unavailable: reclaim claim changed repeatedly"
  return 1
}
acquire_watch_lease() {
  local lock="$PIDFILE.lock" status replacement
  WATCH_PROCESS_START="$(watch_process_start "$$")" || WATCH_PROCESS_START=""
  [[ -n "$WATCH_PROCESS_START" ]] \
    || { log "WATCH identity unavailable: process start cannot be read"; return 1; }
  if [[ -e "$PIDFILE" && ! -f "$lock" ]]; then
    log "WATCH lease unavailable: state exists without ownership lease path=$PIDFILE"
    return 1
  fi
  WATCH_LOCK_CANDIDATE="$lock.next.$$.$RANDOM"
  if ! write_watch_owner "$WATCH_LOCK_CANDIDATE"; then
    WATCH_LOCK_CANDIDATE=""
    log "WATCH lease unavailable: owner identity cannot be written"
    return 1
  fi
  if ln "$WATCH_LOCK_CANDIDATE" "$lock" 2>/dev/null; then
    rm -f "$WATCH_LOCK_CANDIDATE" 2>/dev/null || true
    WATCH_LOCK_CANDIDATE=""
    WATCH_OWNS_LEASE=1
    rm -f "$PIDFILE" 2>/dev/null || true
    return 0
  fi
  [[ -f "$lock" ]] \
    || { log "WATCH lease unavailable: owner identity is absent"; return 1; }
  acquire_watch_reclaim_claim "$WATCH_LOCK_CANDIDATE" || return 1
  rm -f "$WATCH_LOCK_CANDIDATE" 2>/dev/null || true
  WATCH_LOCK_CANDIDATE="$lock.observed.$$.$RANDOM"
  if ! cp "$lock" "$WATCH_LOCK_CANDIDATE" 2>/dev/null \
      || ! cmp -s "$lock" "$WATCH_LOCK_CANDIDATE"; then
    clear_watch_reclaim || true
    log "WATCH lease unavailable: ownership changed during reclamation"
    return 1
  fi
  if watch_lease_owner_status "$WATCH_LOCK_CANDIDATE"; then
    status=0
  else
    status=$?
  fi
  case "$status" in
    0)
      clear_watch_reclaim || true
      log "WATCH already running with a verified lease"
      return 1
      ;;
    2)
      clear_watch_reclaim || true
      log "WATCH lease unavailable: ownership identity is unverifiable"
      return 1
      ;;
  esac
  rm -f "$WATCH_LOCK_CANDIDATE" 2>/dev/null || true
  WATCH_LOCK_CANDIDATE=""
  replacement="$lock.next.$$.$RANDOM"
  WATCH_LOCK_CANDIDATE="$replacement"
  if ! write_watch_owner "$replacement" || ! mv "$replacement" "$lock"; then
    rm -f "$replacement" 2>/dev/null || true
    WATCH_LOCK_CANDIDATE=""
    clear_watch_reclaim || true
    log "WATCH lease unavailable: reclaimed owner identity cannot be written"
    return 1
  fi
  WATCH_LOCK_CANDIDATE=""
  WATCH_OWNS_LEASE=1
  rm -f "$PIDFILE" 2>/dev/null || true
  clear_watch_reclaim || return 1
  return 0
}
watch_lease_belongs_to_current_process() {
  watch_lease_owner_status "$PIDFILE.lock" || return 1
  [[ "$WATCH_OWNER_PID" == "$$" && -n "$WATCH_PROCESS_START" \
      && "$WATCH_OWNER_PROCESS_START" == "$WATCH_PROCESS_START" \
      && "$WATCH_OWNER_CANONICAL_SCRIPT" == "$SCRIPT_PATH" ]]
}
publish_watch_identity() {
  local interval="$1" max="$2" cycle="$3" actual_blob now
  actual_blob="$(compute_shepherd_identity "$LOADED_SCRIPT_PATH" "$SHEPHERD_MODULE_DIR" 2>/dev/null)" \
    || actual_blob=""
  if [[ ! "$WATCH_LOADED_BLOB" =~ ^[0-9a-f]{40}$ \
      || "$actual_blob" != "$WATCH_LOADED_BLOB" ]]; then
    log "WATCH identity mismatch expected=${WATCH_LOADED_BLOB:-missing} actual=${actual_blob:-unreadable}"
    return 1
  fi
  watch_lease_belongs_to_current_process \
    || { log "WATCH lease lost before identity publication"; return 1; }
  WATCH_STATE_OWNER_PID="$$"
  WATCH_STATE_OWNER_START="$WATCH_PROCESS_START"
  WATCH_STATE_INTERVAL="$interval"
  WATCH_STATE_MAX="$max"
  now="$(date '+%s')"
  write_watch_state ready none ready "$now" 0 "$now" ready none "$cycle" \
    || { log "WATCH identity publication failed path=$PIDFILE"; return 1; }
  log "WATCH cycle=$cycle loaded_script_blob=$WATCH_LOADED_BLOB"
}
write_watch_state() {
  local phase="$1" current_pr="$2" current_step="$3" step_started_at="$4"
  local step_deadline_at="$5" last_progress_at="$6" last_outcome="$7"
  local terminal_exit="$8" cycle="$9" temporary="$PIDFILE.next.$$.$RANDOM"
  [[ "$WATCH_STATE_OWNER_PID" =~ ^[1-9][0-9]*$ \
      && -n "$WATCH_STATE_OWNER_START" \
      && "$WATCH_STATE_INTERVAL" =~ ^(0|[1-9][0-9]*)$ \
      && "$WATCH_STATE_MAX" =~ ^[1-9][0-9]*$ \
      && "$WATCH_LOADED_BLOB" =~ ^[0-9a-f]{40}$ ]] || return 1
  if ! watch_lease_owner_status "$PIDFILE.lock"; then return 1; fi
  [[ "$WATCH_OWNER_PID" == "$WATCH_STATE_OWNER_PID" \
      && "$WATCH_OWNER_PROCESS_START" == "$WATCH_STATE_OWNER_START" \
      && "$WATCH_OWNER_CANONICAL_SCRIPT" == "$SCRIPT_PATH" ]] || return 1
  if ! (umask 077; {
      printf 'schema=pr-watch-state-v2\n'
      printf 'pid=%s\n' "$WATCH_STATE_OWNER_PID"
      printf 'process_start=%s\n' "$WATCH_STATE_OWNER_START"
      printf 'canonical_script=%s\n' "$SCRIPT_PATH"
      printf 'loaded_script=%s\n' "$LOADED_SCRIPT_PATH"
      printf 'loaded_blob=%s\n' "$WATCH_LOADED_BLOB"
      printf 'interval=%s\n' "$WATCH_STATE_INTERVAL"
      printf 'max_cycles=%s\n' "$WATCH_STATE_MAX"
      printf 'phase=%s\n' "$phase"
      printf 'current_pr=%s\n' "$current_pr"
      printf 'current_step=%s\n' "$current_step"
      printf 'step_started_at=%s\n' "$step_started_at"
      printf 'step_deadline_at=%s\n' "$step_deadline_at"
      printf 'last_progress_at=%s\n' "$last_progress_at"
      printf 'last_outcome=%s\n' "$last_outcome"
      printf 'cycle=%s\n' "$cycle"
      printf 'terminal_exit=%s\n' "$terminal_exit"
    } > "$temporary") || ! mv "$temporary" "$PIDFILE"; then
    rm -f "$temporary" 2>/dev/null || true
    return 1
  fi
}
load_watch_state() {
  local line key value seen=" " schema="" pid="" process_start="" canonical_script=""
  local loaded_script="" loaded_blob="" interval="" max_cycles=""
  WATCH_STATE_PHASE=""; WATCH_STATE_CURRENT_PR=""; WATCH_STATE_CURRENT_STEP=""
  WATCH_STATE_STEP_STARTED_AT=""; WATCH_STATE_STEP_DEADLINE_AT=""
  WATCH_STATE_LAST_PROGRESS_AT=""; WATCH_STATE_LAST_OUTCOME=""
  WATCH_STATE_CYCLE=""; WATCH_STATE_TERMINAL_EXIT=""
  [[ -f "$PIDFILE" && -r "$PIDFILE" ]] || return 1
  while IFS= read -r line || [[ -n "$line" ]]; do
    key="${line%%=*}"; value="${line#*=}"
    [[ "$line" == *=* && "$seen" != *" $key "* ]] || return 1
    seen+="$key "
    case "$key" in
      schema) schema="$value" ;; pid) pid="$value" ;; process_start) process_start="$value" ;;
      canonical_script) canonical_script="$value" ;; loaded_script) loaded_script="$value" ;;
      loaded_blob) loaded_blob="$value" ;; interval) interval="$value" ;; max_cycles) max_cycles="$value" ;;
      phase) WATCH_STATE_PHASE="$value" ;; current_pr) WATCH_STATE_CURRENT_PR="$value" ;;
      current_step) WATCH_STATE_CURRENT_STEP="$value" ;; step_started_at) WATCH_STATE_STEP_STARTED_AT="$value" ;;
      step_deadline_at) WATCH_STATE_STEP_DEADLINE_AT="$value" ;; last_progress_at) WATCH_STATE_LAST_PROGRESS_AT="$value" ;;
      last_outcome) WATCH_STATE_LAST_OUTCOME="$value" ;; cycle) WATCH_STATE_CYCLE="$value" ;;
      terminal_exit) WATCH_STATE_TERMINAL_EXIT="$value" ;; *) return 1 ;;
    esac
  done < "$PIDFILE"
  [[ "$schema" == pr-watch-state-v2 \
      && "$pid" =~ ^[1-9][0-9]*$ \
      && -n "$process_start" \
      && "$canonical_script" == /* \
      && "$loaded_script" == /* \
      && "$loaded_blob" =~ ^[0-9a-f]{40}$ \
      && "$interval" =~ ^(0|[1-9][0-9]*)$ \
      && "$max_cycles" =~ ^[1-9][0-9]*$ \
      && -n "$WATCH_STATE_PHASE" \
      && -n "$WATCH_STATE_CURRENT_PR" \
      && -n "$WATCH_STATE_CURRENT_STEP" \
      && "$WATCH_STATE_STEP_STARTED_AT" =~ ^(0|[1-9][0-9]*)$ \
      && "$WATCH_STATE_STEP_DEADLINE_AT" =~ ^(0|[1-9][0-9]*)$ \
      && "$WATCH_STATE_LAST_PROGRESS_AT" =~ ^(0|[1-9][0-9]*)$ \
      && -n "$WATCH_STATE_LAST_OUTCOME" \
      && "$WATCH_STATE_CYCLE" =~ ^[1-9][0-9]*$ \
      && "$WATCH_STATE_TERMINAL_EXIT" =~ ^(none|0|[1-9][0-9]{0,2})$ ]] || return 1
  WATCH_STATE_OWNER_PID="$pid"
  WATCH_STATE_OWNER_START="$process_start"
  WATCH_STATE_INTERVAL="$interval"
  WATCH_STATE_MAX="$max_cycles"
  [[ "$canonical_script" == "$SCRIPT_PATH" ]] || return 1
}
watch_step_started() {
  local step="$1" deadline="$2" now
  [[ -n "$WATCH_STATE_OWNER_PID" ]] || return 0
  now="$(date '+%s')"
  write_watch_state working "${CURRENT_PR:-none}" "$step" "$now" "$deadline" "$now" running none \
    "${PR_SHEPHERD_WATCH_CYCLE:-1}"
}
watch_step_finished() {
  local step="$1" outcome="$2" parent_step="${3:-}" parent_started_at="${4:-0}"
  local parent_deadline_at="${5:-0}" now
  [[ -n "$WATCH_STATE_OWNER_PID" ]] || return 0
  now="$(date '+%s')"
  if [[ -n "$parent_step" && "$parent_started_at" =~ ^[0-9]+$ \
      && "$parent_deadline_at" =~ ^[1-9][0-9]*$ ]]; then
    write_watch_state working "${CURRENT_PR:-none}" "$parent_step" \
      "$parent_started_at" "$parent_deadline_at" "$now" "$step-$outcome" none \
      "${PR_SHEPHERD_WATCH_CYCLE:-1}"
    return
  fi
  write_watch_state working "${CURRENT_PR:-none}" "$step" "$now" 0 "$now" "$outcome" none \
    "${PR_SHEPHERD_WATCH_CYCLE:-1}"
}
print_watch_status() {
  local status="$1" reason="$2" state_valid="$3"
  if [[ "$state_valid" == 1 ]]; then
    printf 'status=%s reason=%s state=%s phase=%s current_pr=%s current_step=%s last_progress_at=%s step_deadline_at=%s cycle=%s terminal_exit=%s\n' \
      "$status" "$reason" "$PIDFILE" "$WATCH_STATE_PHASE" "$WATCH_STATE_CURRENT_PR" \
      "$WATCH_STATE_CURRENT_STEP" "$WATCH_STATE_LAST_PROGRESS_AT" \
      "$WATCH_STATE_STEP_DEADLINE_AT" "$WATCH_STATE_CYCLE" "$WATCH_STATE_TERMINAL_EXIT"
  else
    printf 'status=%s reason=%s state=%s last_progress_at=unknown\n' \
      "$status" "$reason" "$PIDFILE"
  fi
}
watch_status() {
  local state_valid=0 owner_status=2 now reason
  if load_watch_state; then state_valid=1; fi
  if [[ ! -f "$PIDFILE.lock" ]]; then
    print_watch_status dead no-owner "$state_valid"
    return 2
  fi
  if watch_lease_owner_status "$PIDFILE.lock"; then owner_status=0; else owner_status=$?; fi
  if [[ "$owner_status" == 1 ]]; then
    print_watch_status dead owner-gone "$state_valid"
    return 2
  fi
  if [[ "$owner_status" == 2 ]]; then
    print_watch_status stalled owner-unverifiable "$state_valid"
    return 1
  fi
  if [[ "$state_valid" != 1 \
      || "$WATCH_STATE_OWNER_PID" != "$WATCH_OWNER_PID" \
      || "$WATCH_STATE_OWNER_START" != "$WATCH_OWNER_PROCESS_START" ]]; then
    print_watch_status stalled state-unverifiable "$state_valid"
    return 1
  fi
  if [[ "$WATCH_STATE_TERMINAL_EXIT" != none ]]; then
    print_watch_status dead terminal "$state_valid"
    return 2
  fi
  now="$(date '+%s')"
  if [[ ! "$now" =~ ^[0-9]+$ ]]; then
    printf 'status=stalled reason=clock-unavailable state=%s\n' "$PIDFILE"
    return 1
  fi
  if [[ "$WATCH_STATE_STEP_DEADLINE_AT" -gt 0 \
      && "$now" -gt "$WATCH_STATE_STEP_DEADLINE_AT" ]]; then
    reason=deadline-exceeded
    printf 'status=stalled reason=%s state=%s phase=%s current_pr=%s current_step=%s last_progress_at=%s step_deadline_at=%s cycle=%s terminal_exit=%s\n' \
      "$reason" "$PIDFILE" "$WATCH_STATE_PHASE" "$WATCH_STATE_CURRENT_PR" "$WATCH_STATE_CURRENT_STEP" \
      "$WATCH_STATE_LAST_PROGRESS_AT" "$WATCH_STATE_STEP_DEADLINE_AT" "$WATCH_STATE_CYCLE" "$WATCH_STATE_TERMINAL_EXIT"
    return 1
  fi
  printf 'status=alive state=%s phase=%s current_pr=%s current_step=%s last_progress_at=%s step_deadline_at=%s cycle=%s terminal_exit=%s\n' \
    "$PIDFILE" "$WATCH_STATE_PHASE" "$WATCH_STATE_CURRENT_PR" "$WATCH_STATE_CURRENT_STEP" \
    "$WATCH_STATE_LAST_PROGRESS_AT" "$WATCH_STATE_STEP_DEADLINE_AT" "$WATCH_STATE_CYCLE" "$WATCH_STATE_TERMINAL_EXIT"
}
remove_watch_snapshot() {
  local snapshot="$1" snapshot_root temporary_directory name
  snapshot_root="$(cd "$(dirname "$snapshot")" 2>/dev/null && pwd -P)" || return 0
  [[ "${snapshot_root##*/}" == pr-shepherd-watch.* ]] || return 0
  temporary_directory="$(cd "${TMPDIR:-/tmp}" 2>/dev/null && pwd -P)" || return 0
  [[ "$(dirname "$snapshot_root")" == "$temporary_directory" ]] || return 0
  rm -f "$snapshot_root/pr-shepherd.sh" 2>/dev/null || true
  for name in "${SHEPHERD_MODULE_NAMES[@]}"; do
    rm -f "$snapshot_root/shepherd/$name" 2>/dev/null || true
  done
  rmdir "$snapshot_root/shepherd" "$snapshot_root" 2>/dev/null || true
}
reload_watch() {
  local interval="$1" max="$2" next_cycle="$3" snapshot_root snapshot blob rc
  local script_repository canonical_directory source_file destination_file
  local script_relative tracked_blob actual_blob name
  if ! snapshot_root="$(mktemp -d "${TMPDIR:-/tmp}/pr-shepherd-watch.XXXXXXXX")"; then
    log "WATCH reload unavailable: immutable snapshot cannot be allocated"
    return 1
  fi
  snapshot="$snapshot_root/pr-shepherd.sh"
  mkdir "$snapshot_root/shepherd" || { rmdir "$snapshot_root"; return 1; }
  script_repository="$(git -C "$(dirname "$SCRIPT_PATH")" rev-parse --show-toplevel 2>/dev/null)" \
    || script_repository=""
  canonical_directory="$(cd "$(dirname "$SCRIPT_PATH")" 2>/dev/null && pwd -P)"
  for name in pr-shepherd.sh "${SHEPHERD_MODULE_NAMES[@]}"; do
    if [[ "$name" == pr-shepherd.sh ]]; then
      source_file="$SCRIPT_PATH"; destination_file="$snapshot"
    else
      source_file="$canonical_directory/shepherd/$name"
      destination_file="$snapshot_root/shepherd/$name"
    fi
    script_relative="$(git -C "$script_repository" ls-files --full-name \
      --error-unmatch -- "$source_file" 2>/dev/null)" || script_relative=""
    tracked_blob="$(git -C "$script_repository" rev-parse "HEAD:$script_relative" 2>/dev/null)" \
      || tracked_blob=""
    actual_blob="$(git hash-object "$source_file" 2>/dev/null)" || actual_blob=""
    if [[ -z "$script_repository" || -z "$script_relative" \
        || ! "$tracked_blob" =~ ^[0-9a-f]{40}$ || "$actual_blob" != "$tracked_blob" ]] \
        || ! cp "$source_file" "$destination_file" 2>/dev/null \
        || ! chmod 0400 "$destination_file" \
        || ! /bin/bash -n "$destination_file"; then
      remove_watch_snapshot "$snapshot"
      log "WATCH reload blocked: canonical script or module does not match tracked HEAD path=$source_file"
      return 1
    fi
  done
  blob="$(compute_shepherd_identity "$snapshot" "$snapshot_root/shepherd" 2>/dev/null)" \
    || blob=""
  if [[ ! "$blob" =~ ^[0-9a-f]{40}$ ]]; then
    remove_watch_snapshot "$snapshot"
    log "WATCH reload unavailable path=$SCRIPT_PATH"
    return 1
  fi
  if [[ -n "$WATCH_LOADED_BLOB" && "$WATCH_LOADED_BLOB" != "$blob" ]]; then
    log "WATCH SCRIPT CHANGED previous_blob=$WATCH_LOADED_BLOB current_blob=$blob"
  fi
  export PR_SHEPHERD_CANONICAL_SCRIPT="$SCRIPT_PATH"
  export PR_SHEPHERD_ROOT="$ROOT"
  export PR_SHEPHERD_WATCH_LOADED_BLOB="$blob"
  export PR_SHEPHERD_WATCH_PREVIOUS_SCRIPT="$LOADED_SCRIPT_PATH"
  export PR_SHEPHERD_WATCH_PROCESS_START="$WATCH_PROCESS_START"
  export PR_SHEPHERD_WATCH_CYCLE="$next_cycle"
  export PR_SHEPHERD_WATCH_OWNER_PID="$$"
  export PR_SHEPHERD_WATCH_OWNER_START="$WATCH_PROCESS_START"
  export PR_SHEPHERD_WATCH_INTERVAL="$interval"
  export PR_SHEPHERD_WATCH_MAX_CYCLES="$max"
  if exec /bin/bash "$snapshot" watch "$interval" "$max"; then
    return 0
  else
    rc=$?
  fi
  rm -f "$snapshot" 2>/dev/null || true
  log "WATCH reload exec failed path=$snapshot exit=$rc"
  return "$rc"
}
cleanup_watch() {
  [[ -z "$WATCH_LOCK_CANDIDATE" ]] \
    || rm -f "$WATCH_LOCK_CANDIDATE" 2>/dev/null || true
  clear_watch_reclaim || true
  remove_watch_snapshot "$LOADED_SCRIPT_PATH"
}
watch_exit_cleanup() {
  local rc=$? now
  [[ -z "$WATCH_SLEEP_PID" ]] || kill -TERM "$WATCH_SLEEP_PID" 2>/dev/null || true
  terminate_active_bounded_tree
  cleanup_supervised_sweep
  if [[ "$WATCH_OWNS_LEASE" == 1 && -n "$WATCH_LOADED_BLOB" ]]; then
    now="$(date '+%s')"
    write_watch_state terminal none exit "$now" 0 "$now" "exit-$rc" "$rc" \
      "${PR_SHEPHERD_WATCH_CYCLE:-1}" || true
  fi
  cleanup_watch
  return "$rc"
}
interrupt_watch() {
  local rc="$1"
  [[ -z "$WATCH_SLEEP_PID" ]] || kill -TERM "$WATCH_SLEEP_PID" 2>/dev/null || true
  terminate_active_bounded_tree
  cleanup_supervised_sweep
  exit "$rc"
}
sweep_worker() {
  trap cleanup_lease_scope EXIT
  trap 'exit 143' TERM
  trap 'exit 130' INT
  sweep
}
cleanup_supervised_sweep() {
  local receipt="${ACTIVE_SWEEP_LEASE_RECEIPT:-}"
  [[ -n "$receipt" ]] || return 0
  release_derived_lease_receipt "$receipt" || true
  rm -f "$receipt" 2>/dev/null || true
  ACTIVE_SWEEP_LEASE_RECEIPT=""
}
terminate_active_bounded_tree() {
  local pid="${ACTIVE_BOUNDED_PID:-}" pgid="" deadline now tree child parent target
  local changed alive attempt
  [[ "$pid" =~ ^[1-9][0-9]*$ ]] || return 0
  tree=" $pid "
  changed=1
  while [[ "$changed" == 1 ]]; do
    changed=0
    while read -r child parent; do
      [[ "$child" =~ ^[1-9][0-9]*$ && "$parent" =~ ^[1-9][0-9]*$ ]] || continue
      if [[ "$tree" == *" $parent "* && "$tree" != *" $child "* ]]; then
        tree+="$child "
        changed=1
      fi
    done < <(ps -axo pid=,ppid= 2>/dev/null)
  done
  pgid="$(ps -p "$pid" -o pgid= 2>/dev/null | tr -d '[:space:]')"
  if [[ "$pgid" == "$pid" ]]; then kill -TERM -- "-$pid" 2>/dev/null || true
  fi
  for target in $tree; do kill -TERM "$target" 2>/dev/null || true; done
  now="$(date '+%s')"; deadline=$((now + KILL_GRACE_SECONDS))
  while :; do
    alive=0
    for target in $tree; do
      if kill -0 "$target" 2>/dev/null; then alive=1; break; fi
    done
    [[ "$alive" == 1 ]] || break
    now="$(date '+%s')"
    [[ "$now" -lt "$deadline" ]] || break
    sleep 0.05
  done
  for target in $tree; do
    kill -KILL "$target" 2>/dev/null || true
  done
  wait "$pid" 2>/dev/null || true
  for attempt in 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20; do
    alive=0
    for target in $tree; do
      if kill -0 "$target" 2>/dev/null; then alive=1; break; fi
    done
    [[ "$alive" == 1 ]] || break
    sleep 0.05
  done
  ACTIVE_BOUNDED_PID=""
}
run_sweep_bounded() {
  local receipt rc=0
  receipt="$(mktemp "${TMPDIR:-/tmp}/pr-shepherd-lease-receipt.XXXXXXXX")" || return 1
  rm -f "$receipt"
  ACTIVE_SWEEP_LEASE_RECEIPT="$receipt"
  if run_bounded sweep sweep "$SWEEP_TIMEOUT_SECONDS" env \
      PR_SHEPHERD_LEASE_RECEIPT="$receipt" \
      /bin/bash "$LOADED_SCRIPT_PATH" sweep-worker; then
    rc=0
  else
    rc=$?
  fi
  cleanup_supervised_sweep
  if [[ "$rc" -ne 0 && "${LAST_BOUNDED_RESULT:-exit}" == timeout && "$DRYRUN" != 1 ]]; then
    mkdir -p "$STATE_DIR"
    record_infrastructure_failure sweep.timeout
  fi
  return "$rc"
}
start_watch() {
  local interval="${1:-60}" max="${2:-360}" launched_pid deadline now status_rc
  [[ "$interval" =~ ^(0|[1-9][0-9]*)$ && "$max" =~ ^[1-9][0-9]*$ ]] \
    || { log "WATCH invalid interval or max_cycles (interval=$interval max_cycles=$max)"; return 2; }
  if watch_status >/dev/null 2>&1; then
    printf 'state=%s status_command=/bin/bash %s status\n' "$PIDFILE" "$SCRIPT_PATH"
    return 0
  else
    status_rc=$?
  fi
  if [[ "$status_rc" == 1 ]]; then
    log "WATCH start rejected: existing worker is stalled"
    return 1
  fi
  nohup /bin/bash "$SCRIPT_PATH" watch "$interval" "$max" \
    >> "$LOG" 2>&1 </dev/null &
  launched_pid=$!
  disown "$launched_pid" 2>/dev/null || true
  now="$(date '+%s')"
  deadline=$((now + API_TIMEOUT_SECONDS))
  while [[ "$now" -le "$deadline" ]]; do
    if watch_status >/dev/null 2>&1; then
      printf 'state=%s status_command=/bin/bash %s status\n' "$PIDFILE" "$SCRIPT_PATH"
      return 0
    fi
    if ! kill -0 "$launched_pid" 2>/dev/null; then
      log "WATCH start failed before ready state=$PIDFILE"
      return 1
    fi
    sleep 0.1
    now="$(date '+%s')"
  done
  kill -TERM "$launched_pid" 2>/dev/null || true
  log "WATCH start timeout_seconds=$API_TIMEOUT_SECONDS state=$PIDFILE"
  return 1
}
watch() {
  local interval="${1:-60}" max="${2:-360}" cycle armed now sleep_deadline
  [[ "$interval" =~ ^(0|[1-9][0-9]*)$ && "$max" =~ ^[1-9][0-9]*$ ]] \
    || { log "WATCH invalid interval or max_cycles (interval=$interval max_cycles=$max)"; return 2; }
  if [[ -z "$WATCH_LOADED_BLOB" ]]; then
    trap watch_exit_cleanup EXIT
    trap 'interrupt_watch 143' TERM
    trap 'interrupt_watch 130' INT
    acquire_watch_lease || return
    reload_watch "$interval" "$max" 1
    return
  fi
  WATCH_OWNS_LEASE=1
  trap watch_exit_cleanup EXIT
  trap 'interrupt_watch 143' TERM
  trap 'interrupt_watch 130' INT
  cycle="${PR_SHEPHERD_WATCH_CYCLE:-}"
  [[ "$cycle" =~ ^[1-9][0-9]*$ && "$cycle" -le "$max" ]] \
    || { log "WATCH reload rejected invalid cycle=${cycle:-missing}"; return 2; }
  watch_lease_belongs_to_current_process \
    || { log "WATCH reload rejected: verified lease is absent"; return 1; }
  publish_watch_identity "$interval" "$max" "$cycle" || return
  remove_watch_snapshot "$WATCH_PREVIOUS_SCRIPT"
  WATCH_PREVIOUS_SCRIPT=""
  if [[ "$cycle" == "1" ]]; then
    log "WATCH start interval=${interval}s max_cycles=${max} pid=$$"
  else
    log "WATCH reloaded cycle=$cycle interval=${interval}s max_cycles=${max} pid=$$"
  fi
  local sweep_outcome=sweep-complete sweep_rc=0
  if run_sweep_bounded; then
    sweep_rc=0
  else
    sweep_rc=$?
    sweep_outcome="sweep-${LAST_BOUNDED_RESULT:-exit}"
    log "SWEEP cycle=$cycle error result=${LAST_BOUNDED_RESULT:-exit} exit=$sweep_rc (continuing)"
  fi
  now="$(date '+%s')"
  sleep_deadline=$((now + interval))
  write_watch_state waiting none sleep "$now" "$sleep_deadline" "$now" "$sweep_outcome" none "$cycle" \
    || { log "WATCH progress publication failed step=sleep"; return 1; }
  sleep "$interval" &
  WATCH_SLEEP_PID=$!
  wait "$WATCH_SLEEP_PID" || true
  WATCH_SLEEP_PID=""
  if [[ "$cycle" -lt "$max" ]]; then
    reload_watch "$interval" "$max" "$((cycle + 1))"
    return
  fi
  if ! armed="$(armed_pr_count)"; then
    log "WATCH renew(${max} 轮耗尽,armed PR 状态不可判,保守重启计数)"
    reload_watch "$interval" "$max" 1
    return
  fi
  if [[ "$armed" -gt 0 ]]; then
    log "WATCH renew(${max} 轮耗尽,仍有 open 且 auto-merge armed PR,重启计数)"
    reload_watch "$interval" "$max" 1
    return
  fi
  log "WATCH end(${max} 轮耗尽,无 open auto-merge armed PR)"
}

validate_configuration || exit $?
case "${1:-}" in
  open)         shift; open_pr "$@" ;;
  start)        shift; start_watch "$@" ;;
  status)       watch_status ;;
  watch)        shift; watch "$@" ;;
  sweep)        run_sweep_bounded ;;
  sweep-worker) sweep_worker ;;
  *) sed -n '2,15p' "$0"; exit 2 ;;
esac
