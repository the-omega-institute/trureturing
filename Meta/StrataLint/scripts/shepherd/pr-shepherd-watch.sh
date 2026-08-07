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
