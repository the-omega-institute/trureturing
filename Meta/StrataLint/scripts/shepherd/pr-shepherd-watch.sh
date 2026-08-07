#!/usr/bin/env bash
# Watch supervision runtime, sourced only by the canonical pr-shepherd entrypoint.

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
      && ( "$loaded_blob" =~ ^[0-9a-f]{40}$ \
        || ( "$loaded_blob" == none && "$WATCH_STATE_PHASE" == terminal ) ) \
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
  now="$(date '+%s')"
  deadline=$((now + API_TIMEOUT_SECONDS))
  while [[ "$now" -le "$deadline" ]]; do
    if watch_status >/dev/null 2>&1; then
      disown "$launched_pid" 2>/dev/null || true
      printf 'state=%s status_command=/bin/bash %s status\n' "$PIDFILE" "$SCRIPT_PATH"
      return 0
    fi
    if ! kill -0 "$launched_pid" 2>/dev/null; then
      wait "$launched_pid" 2>/dev/null || true
      log "WATCH start failed before ready state=$PIDFILE"
      return 1
    fi
    sleep 0.1
    now="$(date '+%s')"
  done
  terminate_process_tree "$launched_pid"
  log "WATCH start timeout_seconds=$API_TIMEOUT_SECONDS state=$PIDFILE"
  return 1
}
