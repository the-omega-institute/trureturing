#!/usr/bin/env bash
# Engine restart decision for the hourly maintenance cycle.
#
# Split out of hourly-maintenance.sh at the SL-003 bucket limit (CLAUDE.md 8:
# split, do not migrate). Sourced into the parent shell, so it shares the
# parent's globals (FKST_* host contract values, CHANGED, ACTIVATION_ROLLBACK_REV)
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

  if [[ "$ACTIVATION_ROLLBACK_REV" =~ ^[0-9a-f]{40}$ \
      && -z "$pid" && "$launchd_state" == "not-in-service" ]]; then
    if rollback_platform "$ACTIVATION_ROLLBACK_REV"; then
      bash "$FKST_RUN_SCRIPT" stop >/dev/null 2>&1
      sleep 8
      say "reverted platform to ${ACTIVATION_ROLLBACK_REV:0:12}"
    else
      say "PLATFORM-ROLLBACK-FAIL after confirmed startup failure; previous revision not fully activated"
    fi
  elif [[ "$ACTIVATION_ROLLBACK_REV" =~ ^[0-9a-f]{40}$ ]]; then
    say "PLATFORM-ROLLBACK-SKIPPED: restart budget expired but startup failure not confirmed (launchd=$launchd_state last_pid=${pid:-none})"
  fi
  return 1
}

restart_defer_state_path() {
  printf '%s\n' "$FKST_RUNTIME_ROOT/hourly-maintenance.restart-defer-since"
}

pending_activation_state_path() {
  printf '%s\n' "$FKST_RUNTIME_ROOT/hourly-maintenance.pending-activation"
}

timestamp_is_usable() {
  local value="$1" now="$2"
  [[ "$value" =~ ^(0|[1-9][0-9]*)$ && "$now" =~ ^(0|[1-9][0-9]*)$ ]] || return 1
  if [[ "${#value}" -lt "${#now}" ]]; then
    return 0
  fi
  [[ "${#value}" -eq "${#now}" \
    && ( "$value" == "$now" || "$value" < "$now" ) ]]
}

load_pending_activation() {
  local path="$1" line now generation created_at previous_rev target_rev
  local -a lines=()
  [[ -f "$path" && -r "$path" ]] || return 1
  while IFS= read -r line || [[ -n "$line" ]]; do
    lines+=("$line")
  done < "$path"
  [[ "${#lines[@]}" -eq 4 \
    && "${lines[0]}" == generation=* \
    && "${lines[1]}" == created_at=* \
    && "${lines[2]}" == previous_platform_rev=* \
    && "${lines[3]}" == target_platform_rev=* ]] || return 1

  generation="${lines[0]#generation=}"
  created_at="${lines[1]#created_at=}"
  previous_rev="${lines[2]#previous_platform_rev=}"
  target_rev="${lines[3]#target_platform_rev=}"
  now="$(date -u +%s)" || return 1
  [[ "$generation" =~ ^[0-9]+-[0-9]+-[0-9]+$ ]] || return 1
  timestamp_is_usable "$created_at" "$now" || return 1
  if [[ "$previous_rev" == "none" ]]; then
    [[ "$target_rev" == "none" ]] || return 1
  else
    [[ "$previous_rev" =~ ^[0-9a-f]{40}$ \
      && "$target_rev" =~ ^[0-9a-f]{40}$ ]] || return 1
  fi

  PENDING_ACTIVATION_GENERATION="$generation"
  PENDING_ACTIVATION_PREVIOUS_REV="$previous_rev"
  PENDING_ACTIVATION_TARGET_REV="$target_rev"
}

record_pending_activation() {
  local previous_rev="$1" target_rev="$2" reason="$3"
  local pending_path lock_path temporary now generation existing_previous existing_target
  pending_path="$(pending_activation_state_path)"
  lock_path="${pending_path}.lock"
  [[ -d "$FKST_RUNTIME_ROOT" ]] || {
    say "RESTART-PENDING-STATE-FAIL: runtime root is unavailable; refusing $reason"
    return 1
  }
  if ! mkdir "$lock_path" 2>/dev/null; then
    say "RESTART-PENDING-STATE-FAIL: activation record is locked; refusing $reason"
    return 1
  fi

  if [[ -e "$pending_path" ]]; then
    if ! load_pending_activation "$pending_path"; then
      rmdir "$lock_path" 2>/dev/null || true
      say "RESTART-PENDING-STATE-FAIL: existing activation record is invalid; refusing $reason"
      return 1
    fi
    existing_previous="$PENDING_ACTIVATION_PREVIOUS_REV"
    existing_target="$PENDING_ACTIVATION_TARGET_REV"
    if [[ "$existing_previous" != "none" ]]; then
      previous_rev="$existing_previous"
      [[ -n "$target_rev" ]] || target_rev="$existing_target"
    fi
  fi

  [[ -n "$previous_rev" ]] || previous_rev="none"
  [[ -n "$target_rev" ]] || target_rev="none"
  if [[ "$previous_rev" == "none" ]]; then
    if [[ "$target_rev" != "none" ]]; then
      rmdir "$lock_path" 2>/dev/null || true
      say "RESTART-PENDING-STATE-FAIL: activation record has no rollback origin; refusing $reason"
      return 1
    fi
  elif [[ ! "$previous_rev" =~ ^[0-9a-f]{40}$ \
      || ! "$target_rev" =~ ^[0-9a-f]{40}$ ]]; then
    rmdir "$lock_path" 2>/dev/null || true
    say "RESTART-PENDING-STATE-FAIL: activation revisions are invalid; refusing $reason"
    return 1
  fi

  now="$(date -u +%s)" || now=""
  if ! timestamp_is_usable "$now" "$now"; then
    rmdir "$lock_path" 2>/dev/null || true
    say "RESTART-PENDING-STATE-FAIL: cannot read a usable clock; refusing $reason"
    return 1
  fi
  generation="${now}-$$-${RANDOM}"
  temporary="${pending_path}.next-${generation}"
  if ! (set -o noclobber; {
      printf 'generation=%s\n' "$generation"
      printf 'created_at=%s\n' "$now"
      printf 'previous_platform_rev=%s\n' "$previous_rev"
      printf 'target_platform_rev=%s\n' "$target_rev"
    } > "$temporary") 2>/dev/null \
      || ! mv "$temporary" "$pending_path"; then
    rm -f -- "$temporary"
    rmdir "$lock_path" 2>/dev/null || true
    say "RESTART-PENDING-STATE-FAIL: cannot persist activation obligation; refusing $reason"
    return 1
  fi

  ACTIVATION_ROLLBACK_REV="$([[ "$previous_rev" == "none" ]] || printf '%s' "$previous_rev")"
  if ! rmdir "$lock_path" 2>/dev/null; then
    say "RESTART-PENDING-LOCK-RELEASE-FAIL: generation $generation is durable but locked"
    return 1
  fi
  say "ACTIVATION-PENDING: recorded generation $generation before $reason"
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

ensure_timestamp_state() {
  local state_path="$1" now="$2"
  if [[ -e "$state_path" ]]; then
    [[ -f "$state_path" ]]
    return
  fi
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
  if ! ensure_timestamp_state "$state_path" "$now"; then
    say "FORCE-RESTART: cannot record bounded defer state; applying pending pin"
    return 1
  fi
  since="$(head -1 "$state_path" 2>/dev/null)"
  if ! timestamp_is_usable "$since" "$now"; then
    say "FORCE-RESTART: invalid defer state; applying pending pin"
    return 1
  fi

  age=$((10#$now - 10#$since))
  if [[ "$age" -ge "$FKST_CODEX_TIMEOUT_IMPLEMENT" ]]; then
    say "FORCE-RESTART: defer bound reached ($reason; age=${age}s bound=${FKST_CODEX_TIMEOUT_IMPLEMENT}s); applying pending pin"
    return 1
  fi
  say "DEFER-RESTART: $reason + engine alive (pid $alive); defer_age=${age}s bound=${FKST_CODEX_TIMEOUT_IMPLEMENT}s"
  return 0
}

clear_pending_activation() {
  local pending_path="$1" defer_path="$2" verified_generation="$3"
  local lock_path="${pending_path}.lock" current_generation
  if ! mkdir "$lock_path" 2>/dev/null; then
    say "ACTIVATION-RETAINED: restart verified but activation record is locked"
    return 1
  fi

  if load_pending_activation "$pending_path"; then
    current_generation="$PENDING_ACTIVATION_GENERATION"
    if [[ "$verified_generation" == "invalid" \
        || "$current_generation" != "$verified_generation" ]]; then
      rmdir "$lock_path" 2>/dev/null || true
      say "ACTIVATION-RETAINED: verified generation $verified_generation was superseded by $current_generation"
      return 0
    fi
  elif [[ "$verified_generation" != "invalid" ]]; then
    rmdir "$lock_path" 2>/dev/null || true
    say "ACTIVATION-RETAINED: verified generation $verified_generation changed to invalid state"
    return 0
  fi

  if ! rm -f -- "$defer_path"; then
    rmdir "$lock_path" 2>/dev/null || true
    say "ACTIVATION-RETAINED: restart verified but defer state could not be cleared"
    return 1
  fi
  if ! rm -f -- "$pending_path" || [[ -e "$pending_path" ]]; then
    rmdir "$lock_path" 2>/dev/null || true
    say "ACTIVATION-RETAINED: restart verified but pending obligation could not be cleared"
    return 1
  fi
  if ! rmdir "$lock_path" 2>/dev/null; then
    say "ACTIVATION-CLEAR-LOCK-FAIL: generation $verified_generation cleared but lock remained"
    return 1
  fi
  say "ACTIVATION-CLEARED: restart verified generation $verified_generation with a new pid and launchd in service"
}

restart_if_needed() {
  local pending_path defer_path alive implementing reason verified_generation
  pending_path="$(pending_activation_state_path)"
  defer_path="$(restart_defer_state_path)"

  if [[ "$CHANGED" == "1" ]]; then
    if [[ -e "$pending_path" ]]; then
      say "ACTIVATION-PENDING: change detected; durable obligation already recorded"
    else
      say "ACTIVATION-INTENT-MISSING: changed state has no write-ahead obligation; recovering before restart"
      if ! record_pending_activation \
          "${PLATFORM_CURRENT_REV:-}" "${PLATFORM_DEV_REV:-}" "post-mutation intent recovery"; then
        say "RESTART-PENDING-STATE-FAIL: cannot persist activation obligation; restarting immediately"
        if restart_engine; then
          say "ACTIVATION-VERIFIED: immediate restart succeeded after persistence failure"
          return 0
        fi
        say "ACTIVATION-UNRECORDED: immediate restart failed after persistence failure"
        return 1
      fi
    fi
  fi

  if [[ ! -e "$pending_path" ]]; then
    if [[ -e "$defer_path" ]]; then
      if ! record_pending_activation "" "" "orphaned defer-state recovery"; then
        say "ACTIVATION-PENDING-RECOVERY-FAIL: defer state exists but its obligation marker cannot be restored; restarting immediately"
        if restart_engine; then
          if ! rm -f -- "$defer_path"; then
            say "ACTIVATION-RETAINED: restart verified but orphaned defer state could not be cleared"
            return 1
          fi
          say "ACTIVATION-CLEARED: orphaned defer evidence resolved by a verified restart"
          return 0
        fi
        say "ACTIVATION-RETAINED: restart failed while recovering orphaned defer evidence"
        return 1
      fi
      say "ACTIVATION-PENDING-RECOVERED: defer state existed without its obligation marker"
    else
      say "ALL CURRENT; no restart"
      return 0
    fi
  fi

  if load_pending_activation "$pending_path"; then
    verified_generation="$PENDING_ACTIVATION_GENERATION"
    if [[ "$PENDING_ACTIVATION_PREVIOUS_REV" == "none" ]]; then
      ACTIVATION_ROLLBACK_REV=""
    else
      ACTIVATION_ROLLBACK_REV="$PENDING_ACTIVATION_PREVIOUS_REV"
      PLATFORM_CURRENT_REV="$PENDING_ACTIVATION_PREVIOUS_REV"
      PLATFORM_DEV_REV="$PENDING_ACTIVATION_TARGET_REV"
    fi
  else
    verified_generation="invalid"
    ACTIVATION_ROLLBACK_REV=""
    say "ACTIVATION-PENDING-STATE-INVALID: retaining and re-evaluating the obligation"
  fi
  if [[ "$CHANGED" == "0" ]]; then
    say "ACTIVATION-PENDING: retrying durable obligation generation $verified_generation on a current-pin cycle"
  fi

  alive="$(engine_pid)"
  if [[ -n "$alive" ]]; then
    if implementing="$(active_local_implement_count "$alive")"; then
      if [[ ! "$implementing" =~ ^[0-9]+$ ]]; then
        reason="local implement execution state is invalid"
        defer_restart_with_bound "$reason" "$alive" "$defer_path" && return 0
      elif [[ "$implementing" -gt 0 ]]; then
        reason="$implementing local implement child process(es) active"
        defer_restart_with_bound "$reason" "$alive" "$defer_path" && return 0
      fi
    else
      reason="local implement execution state unavailable"
      defer_restart_with_bound "$reason" "$alive" "$defer_path" && return 0
    fi
  fi

  if restart_engine; then
    clear_pending_activation "$pending_path" "$defer_path" "$verified_generation"
    return
  fi
  say "ACTIVATION-RETAINED: restart failed; durable obligation will be retried"
  return 1
}
