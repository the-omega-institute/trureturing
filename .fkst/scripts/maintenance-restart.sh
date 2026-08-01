#!/usr/bin/env bash
# Engine restart decision for the hourly maintenance cycle.
#
# Split out of hourly-maintenance.sh at the SL-003 bucket limit (CLAUDE.md 8:
# split, do not migrate). Sourced into the parent shell, so it shares the
# parent's globals (FKST_* host contract values, CHANGED, PLATFORM_CHANGED)
# and its `say` reporter exactly as before.

engine_pid() {
  local escaped_root
  escaped_root="$(printf '%s' "$FKST_HOST_ROOT" | sed 's/[][\\.^$*+?{}|()]/\\&/g')"
  pgrep -f "fkst-framework.*supervise --project-root $escaped_root" 2>/dev/null | head -1
}

launchd_service_state() {
  local output line
  if ! output="$(launchctl list 2>/dev/null)"; then
    printf 'unknown\n'
    return 0
  fi
  while IFS= read -r line; do
    if [[ "$line" == *[[:space:]]"$FKST_LAUNCHD_LABEL" ]]; then
      printf 'in-service\n'
      return 0
    fi
  done <<< "$output"
  printf 'not-in-service\n'
}

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

restart_defer_state_path() {
  printf '%s\n' "$FKST_RUNTIME_ROOT/hourly-maintenance.restart-defer-since"
}

current_supervisor_log() {
  local engine_pid_value="$1" candidate newest=""
  for candidate in "$FKST_RUNTIME_ROOT"/logs/supervisor-*-"$engine_pid_value".log; do
    [[ -f "$candidate" && -r "$candidate" ]] || continue
    if [[ -z "$newest" || "$candidate" -nt "$newest" ]]; then
      newest="$candidate"
    fi
  done
  [[ -n "$newest" ]] || return 1
  printf '%s\n' "$newest"
}

active_local_implement_count() {
  local engine_pid_value="$1" supervisor_log pids pid count=0
  supervisor_log="$(current_supervisor_log "$engine_pid_value")" || return 1
  pids="$(awk '
    function value(name, field_index, prefix) {
      prefix = name "="
      for (field_index = 1; field_index <= NF; field_index++) {
        if (index($field_index, prefix) == 1) {
          return substr($field_index, length(prefix) + 1)
        }
      }
      return ""
    }
    $1 == "event=dept_child_spawn" && value("dept") == "github-devloop.implement" {
      pid = value("pid")
      if (pid ~ /^[0-9]+$/) active[pid] = 1
      next
    }
    $1 == "event=dept_child_exit" && value("dept") == "github-devloop.implement" {
      pid = value("pid")
      if (pid ~ /^[0-9]+$/) delete active[pid]
    }
    END { for (pid in active) print pid }
  ' "$supervisor_log")" || return 1

  while IFS= read -r pid; do
    [[ "$pid" =~ ^[0-9]+$ ]] || continue
    kill -0 "$pid" 2>/dev/null && count=$((count + 1))
  done <<< "$pids"
  printf '%s\n' "$count"
}

ensure_restart_pending() {
  local state_path="$1" now="$2"
  [[ -e "$state_path" ]] && return 0
  [[ -d "$FKST_RUNTIME_ROOT" ]] || return 1
  (set -o noclobber; printf '%s\n' "$now" > "$state_path") 2>/dev/null \
    || [[ -f "$state_path" ]]
}

defer_restart_with_bound() {
  local reason="$1" alive="$2" state_path="$3" now since age
  now="$(date -u +%s)" || {
    say "FORCE-RESTART: cannot read clock for defer bound; applying pending pin"
    return 1
  }
  if ! ensure_restart_pending "$state_path" "$now"; then
    say "FORCE-RESTART: cannot record bounded defer state; applying pending pin"
    return 1
  fi
  since="$(head -1 "$state_path" 2>/dev/null)"
  if [[ ! "$since" =~ ^[0-9]+$ || "$since" -gt "$now" ]]; then
    say "FORCE-RESTART: invalid defer state; applying pending pin"
    return 1
  fi

  age=$((now - since))
  if [[ "$age" -ge "$FKST_CODEX_TIMEOUT_IMPLEMENT" ]]; then
    say "FORCE-RESTART: defer bound reached ($reason; age=${age}s bound=${FKST_CODEX_TIMEOUT_IMPLEMENT}s); applying pending pin"
    return 1
  fi
  say "DEFER-RESTART: $reason + engine alive (pid $alive); defer_age=${age}s bound=${FKST_CODEX_TIMEOUT_IMPLEMENT}s"
  cleanup_old_backups
  return 0
}

restart_if_needed() {
  local state_path alive implementing reason now
  state_path="$(restart_defer_state_path)"
  if [[ "$CHANGED" == "0" && ! -e "$state_path" ]]; then
    say "ALL CURRENT; no restart"
    return 0
  fi

  if [[ "$CHANGED" == "1" && ! -e "$state_path" ]]; then
    now="$(date -u +%s)" || now=""
    if [[ ! "$now" =~ ^[0-9]+$ ]] \
        || ! ensure_restart_pending "$state_path" "$now"; then
      say "RESTART-PENDING-STATE-FAIL: cannot persist pending restart; restarting immediately"
      restart_engine
      return
    fi
  fi

  alive="$(engine_pid)"
  if [[ -n "$alive" ]]; then
    if implementing="$(active_local_implement_count "$alive")"; then
      if [[ "$implementing" -gt 0 ]]; then
        reason="$implementing local implement child process(es) active"
        defer_restart_with_bound "$reason" "$alive" "$state_path" && return 0
      fi
    else
      reason="local implement execution state unavailable"
      defer_restart_with_bound "$reason" "$alive" "$state_path" && return 0
    fi
  fi

  if restart_engine; then
    rm -f -- "$state_path"
    return 0
  fi
  return 1
}
