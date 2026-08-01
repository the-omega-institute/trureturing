#!/usr/bin/env bash
# Restart policy for the canonical maintenance cycle: engine stop/start with a health
# budget, and deferral bounded by engine-owned implement leases.

restart_engine() {
  local budget="${FKST_RESTART_TIMEOUT_SECONDS:-180}"
  local poll_interval="${FKST_RESTART_POLL_SECONDS:-5}"
  if [[ ! "$budget" =~ ^[1-9][0-9]*$ \
      || ! "$poll_interval" =~ ^[1-9][0-9]*$ ]]; then
    say "RESTART-CONFIG-FAIL: timeout and poll interval must be positive integers (timeout=$budget poll=$poll_interval)"
    return 1
  fi

  local previous_pid elapsed=0 launchd_state pid wait_seconds health_state
  previous_pid="$(engine_pid)"
  if ! bash "$FKST_RUN_SCRIPT" stop >/dev/null 2>&1; then
    say "RESTART-STOP-FAIL; engine state unchanged"
    return 1
  fi

  while true; do
    launchd_state="$(launchd_service_state)"
    pid="$(engine_pid)"
    if [[ "$launchd_state" == "in-service" && -n "$pid" \
        && ( -z "$previous_pid" || "$pid" != "$previous_pid" ) ]]; then
      say "SYNCED OK (engine pid $pid; platform ${PLATFORM_DEV_REV:0:12}; checkout $([ -n "$CHECKOUT_DEV_REV" ] && printf '%s' "${CHECKOUT_DEV_REV:0:12}" || printf 'n/a'))"
      cleanup_old_backups
      return 0
    fi
    [[ "$elapsed" -lt "$budget" ]] || break

    wait_seconds="$poll_interval"
    if [[ $((elapsed + wait_seconds)) -gt "$budget" ]]; then
      wait_seconds=$((budget - elapsed))
    fi
    if ! sleep "$wait_seconds"; then
      say "RESTART-WAIT-FAIL after ${elapsed}s (budget=${budget}s launchd=$launchd_state last_pid=${pid:-none})"
      return 1
    fi
    elapsed=$((elapsed + wait_seconds))
  done

  if [[ -z "$pid" && "$launchd_state" == "not-in-service" ]]; then
    health_state="launchd-not-in-service"
  elif [[ -z "$pid" ]]; then
    health_state="waiting-for-new-pid"
  elif [[ -n "$previous_pid" && "$pid" == "$previous_pid" ]]; then
    health_state="old-pid-still-present"
  elif [[ "$launchd_state" == "not-in-service" ]]; then
    health_state="new-pid-without-launchd-service"
  else
    health_state="launchd-status-unknown"
  fi
  say "UNHEALTHY after restart (state=$health_state waited=${elapsed}s budget=${budget}s launchd=$launchd_state old_pid=${previous_pid:-none} last_pid=${pid:-none})"

  if [[ "$PLATFORM_CHANGED" == "1" \
      && -z "$pid" && "$launchd_state" == "not-in-service" ]]; then
    if rollback_platform; then
      bash "$FKST_RUN_SCRIPT" stop >/dev/null 2>&1
      sleep 8
      say "reverted platform to ${PLATFORM_CURRENT_REV:0:12}"
    else
      say "PLATFORM-ROLLBACK-FAIL after confirmed startup failure; original bytes not confirmed"
    fi
  elif [[ "$PLATFORM_CHANGED" == "1" ]]; then
    say "PLATFORM-ROLLBACK-SKIPPED: restart budget expired but startup failure not confirmed (launchd=$launchd_state last_pid=${pid:-none})"
  fi
  return 1
}

implement_lease_count() {
  local lock owner count=0
  if [[ -n "${FKST_REPORT_SLOT_ROOT:-}" && -d "$FKST_REPORT_SLOT_ROOT" ]]; then
    for lock in "$FKST_REPORT_SLOT_ROOT"/*.lock; do
      [[ -e "$lock/owner" ]] || continue
      owner="$(grep -oE '^[0-9]+' "$lock/owner" 2>/dev/null | head -1)"
      [[ -n "$owner" ]] || continue
      kill -0 "$owner" 2>/dev/null || continue
      count=$((count + 1))
    done
  fi
  printf '%s\n' "$count"
}

restart_defer_state_path() {
  printf '%s\n' \
    "${FKST_RESTART_DEFER_STATE:-$(dirname -- "$FKST_MAINTENANCE_LOG")/restart-defer.state}"
}

restart_defer_bound_seconds() {
  local bound="${FKST_RESTART_DEFER_MAX_SECONDS:-21600}"
  [[ "$bound" =~ ^[0-9]+$ ]] || bound=21600
  printf '%s\n' "$bound"
}

restart_if_needed() {
  local state
  state="$(restart_defer_state_path)"
  if [[ "$CHANGED" == "0" ]]; then
    say "ALL CURRENT; no restart"
    rm -f -- "$state" 2>/dev/null || true
    return 0
  fi

  local alive leases bound started now elapsed
  alive="$(engine_pid)"
  if [[ -n "$alive" ]]; then
    leases="$(implement_lease_count)"
    if [[ "$leases" -gt 0 ]]; then
      bound="$(restart_defer_bound_seconds)"
      now="$(date +%s)"
      started="$(grep -oE '^[0-9]+' "$state" 2>/dev/null | head -1)"
      if [[ -z "$started" || "$started" -gt "$now" ]]; then
        started="$now"
        printf '%s\n' "$started" > "$state" 2>/dev/null || true
      fi
      elapsed=$((now - started))
      if [[ "$elapsed" -lt "$bound" ]]; then
        say "DEFER-RESTART: $leases live implement lease(s) + engine alive (pid $alive); deferred ${elapsed}s of ${bound}s bound"
        cleanup_old_backups
        return 0
      fi
      say "FORCE-RESTART: defer bound exceeded (elapsed=${elapsed}s bound=${bound}s leases=$leases); draining and restarting"
    fi
  fi

  rm -f -- "$state" 2>/dev/null || true
  restart_engine
}

