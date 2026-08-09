#!/usr/bin/env bash
# Watch supervision runtime, sourced only by the canonical pr-shepherd entrypoint.

load_watch_state() {
  local line key value seen=" " schema="" pid="" process_start="" canonical_script=""
  local loaded_script="" loaded_blob="" interval="" max_cycles=""
  WATCH_STATE_PHASE=""; WATCH_STATE_CURRENT_PR=""; WATCH_STATE_CURRENT_STEP=""
  WATCH_STATE_STEP_STARTED_AT=""; WATCH_STATE_STEP_DEADLINE_AT=""
  WATCH_STATE_LAST_PROGRESS_AT=""; WATCH_STATE_LAST_OUTCOME=""
  WATCH_STATE_CYCLE=""; WATCH_STATE_TERMINAL_EXIT=""
  WATCH_STATE_CANONICAL_SCRIPT=""
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
  WATCH_STATE_CANONICAL_SCRIPT="$canonical_script"
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
watch_dead_reason() {
  local state_valid="$1" fallback="$2"
  if [[ "$state_valid" == 1 \
      && "$WATCH_STATE_TERMINAL_EXIT" != none \
      && "$WATCH_STATE_LAST_OUTCOME" == watch-reload-fetch-retries-exhausted ]]; then
    printf 'reload-fetch-retries-exhausted'
  else
    printf '%s' "$fallback"
  fi
}
watch_status() {
  local state_valid=0 owner_status=2 now reason
  if load_watch_state; then state_valid=1; fi
  if [[ ! -f "$PIDFILE.lock" ]]; then
    reason="$(watch_dead_reason "$state_valid" no-owner)"
    print_watch_status dead "$reason" "$state_valid"
    return 2
  fi
  if watch_lease_owner_status "$PIDFILE.lock"; then owner_status=0; else owner_status=$?; fi
  if [[ "$owner_status" == 1 ]]; then
    reason="$(watch_dead_reason "$state_valid" owner-gone)"
    print_watch_status dead "$reason" "$state_valid"
    return 2
  fi
  if [[ "$owner_status" == 2 ]]; then
    print_watch_status stalled owner-unverifiable "$state_valid"
    return 1
  fi
  if [[ "$state_valid" != 1 \
      || "$WATCH_STATE_OWNER_PID" != "$WATCH_OWNER_PID" \
      || "$WATCH_STATE_OWNER_START" != "$WATCH_OWNER_PROCESS_START" \
      || "$WATCH_STATE_CANONICAL_SCRIPT" != "$WATCH_OWNER_CANONICAL_SCRIPT" ]]; then
    print_watch_status stalled state-unverifiable "$state_valid"
    return 1
  fi
  if [[ "$WATCH_STATE_TERMINAL_EXIT" != none ]]; then
    reason="$(watch_dead_reason "$state_valid" terminal)"
    print_watch_status dead "$reason" "$state_valid"
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
  local rc=$? now marker="${WATCH_TERMINAL_OUTCOME:-}"
  [[ -z "$WATCH_SLEEP_PID" ]] || kill -TERM "$WATCH_SLEEP_PID" 2>/dev/null || true
  terminate_active_bounded_tree
  cleanup_supervised_sweep
  if [[ "$WATCH_OWNS_LEASE" == 1 && -n "$WATCH_LOADED_BLOB" ]]; then
    now="$(date '+%s')"
    [[ -n "$marker" ]] || marker="exit-$rc"
    write_watch_state terminal none exit "$now" 0 "$now" "$marker" "$rc" \
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
watch() {
  local interval="${1:-60}" max="${2:-360}" cycle armed now sleep_deadline
  [[ "$interval" =~ ^(0|[1-9][0-9]*)$ && "$max" =~ ^[1-9][0-9]*$ ]] \
    || { log "WATCH invalid interval or max_cycles (interval=$interval max_cycles=$max)"; return 2; }
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
  remove_watch_snapshot "$WATCH_PREVIOUS_SCRIPT"; WATCH_PREVIOUS_SCRIPT=""
  if [[ "$cycle" == 1 ]]; then log "WATCH start interval=${interval}s max_cycles=${max} pid=$$"
  else log "WATCH reloaded cycle=$cycle interval=${interval}s max_cycles=${max} pid=$$"; fi
  local sweep_outcome=sweep-complete sweep_rc=0
  if run_sweep_bounded; then sweep_rc=0
  else
    sweep_rc=$?; sweep_outcome="sweep-${LAST_BOUNDED_RESULT:-exit}"
    log "SWEEP cycle=$cycle error result=${LAST_BOUNDED_RESULT:-exit} exit=$sweep_rc (continuing)"
  fi
  now="$(date '+%s')"; sleep_deadline=$((now + interval))
  write_watch_state waiting none sleep "$now" "$sleep_deadline" "$now" "$sweep_outcome" none "$cycle" \
    || { log "WATCH progress publication failed step=sleep"; return 1; }
  sleep "$interval" & WATCH_SLEEP_PID=$!
  wait "$WATCH_SLEEP_PID" || true; WATCH_SLEEP_PID=""
  if [[ "$cycle" -lt "$max" ]]; then reload_watch "$interval" "$max" "$((cycle + 1))"; return; fi
  if ! armed="$(armed_pr_count)"; then
    log "WATCH renew(${max} 轮耗尽,armed PR 状态不可判,保守重启计数)"
    reload_watch "$interval" "$max" 1; return
  fi
  if [[ "$armed" -gt 0 ]]; then
    log "WATCH renew(${max} 轮耗尽,仍有 open 且 auto-merge armed PR,重启计数)"
    reload_watch "$interval" "$max" 1; return
  fi
  log "WATCH end(${max} 轮耗尽,无 open auto-merge armed PR)"
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
  local runtime_stdout runtime_stderr
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
  now="$(date '+%s')"
  create_step_artifacts watch-runtime "$now" \
    || { log "WATCH start failed: runtime artifact unavailable"; return 1; }
  runtime_stdout="$LAST_BOUNDED_STDOUT_ARTIFACT"; runtime_stderr="$LAST_BOUNDED_STDERR_ARTIFACT"
  log "WATCH_BACKGROUND stdout_artifact=$runtime_stdout stderr_artifact=$runtime_stderr"
  nohup /bin/bash "$SCRIPT_PATH" watch "$interval" "$max" \
    > "$runtime_stdout" 2> "$runtime_stderr" </dev/null &
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
