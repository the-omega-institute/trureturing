#!/usr/bin/env bash
# Watch supervision runtime, sourced only by the canonical pr-shepherd entrypoint.

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
