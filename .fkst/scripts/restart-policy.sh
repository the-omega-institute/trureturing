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

restart_activation_state_path() {
  printf '%s\n' \
    "${FKST_RESTART_ACTIVATION_STATE:-$(dirname -- "$FKST_MAINTENANCE_LOG")/restart-activation.state}"
}

canonical_decimal_at_most() {
  local value="$1" maximum="$2" index value_digit maximum_digit
  [[ "$value" =~ ^(0|[1-9][0-9]*)$ ]] || return 1
  if [[ "${#value}" -lt "${#maximum}" ]]; then
    return 0
  fi
  [[ "${#value}" -eq "${#maximum}" ]] || return 1
  for ((index = 0; index < ${#value}; index++)); do
    value_digit="${value:index:1}"
    maximum_digit="${maximum:index:1}"
    [[ "$value_digit" == "$maximum_digit" ]] && continue
    ((10#$value_digit < 10#$maximum_digit))
    return
  done
  return 0
}

timestamp_is_usable() {
  local value="$1" now="$2"
  canonical_decimal_at_most "$now" 9223372036854775807 || return 1
  canonical_decimal_at_most "$value" "$now"
}

restart_defer_bound_seconds() {
  local bound="${FKST_RESTART_DEFER_MAX_SECONDS:-21600}"
  canonical_decimal_at_most "$bound" 9223372036854775807 || bound=21600
  printf '%s\n' "$bound"
}

restart_state_lock_acquire() {
  local state="$1" lock candidate reclaim owner token attempt
  lock="${state}.lock"
  token="$$-$(date -u +%s 2>/dev/null)-$RANDOM"
  candidate="${lock}.claim-$token"
  printf '%s %s\n' "$$" "$token" > "$candidate" 2>/dev/null || return 1

  for attempt in 1 2; do
    if ln "$candidate" "$lock" 2>/dev/null; then
      rm -f -- "$candidate"
      RESTART_STATE_LOCK_PATH="$lock"
      RESTART_STATE_LOCK_TOKEN="$token"
      return 0
    fi
    read -r owner _ < "$lock" 2>/dev/null || owner=""
    if [[ "$owner" =~ ^[1-9][0-9]*$ ]] && kill -0 "$owner" 2>/dev/null; then
      break
    fi
    reclaim="${lock}.reclaim-$token"
    if mv "$lock" "$reclaim" 2>/dev/null; then
      rm -f -- "$reclaim"
      continue
    fi
    break
  done
  rm -f -- "$candidate"
  return 1
}

restart_state_lock_release() {
  local owner token
  read -r owner token < "$RESTART_STATE_LOCK_PATH" 2>/dev/null || return 1
  [[ "$token" == "$RESTART_STATE_LOCK_TOKEN" ]] || return 1
  rm -f -- "$RESTART_STATE_LOCK_PATH"
}

load_restart_obligation() {
  local path="$1" line now generation created_at previous_revision target_revision
  local checkout_previous_revision checkout_target_revision lean_report_required
  local -a lines=()
  [[ -f "$path" && -r "$path" ]] || return 1
  while IFS= read -r line || [[ -n "$line" ]]; do
    lines+=("$line")
  done < "$path"
  [[ "${#lines[@]}" -eq 7 \
      && "${lines[0]}" == generation=* \
      && "${lines[1]}" == created_at=* \
      && "${lines[2]}" == previous_platform_rev=* \
      && "${lines[3]}" == target_platform_rev=* \
      && "${lines[4]}" == checkout_previous_rev=* \
      && "${lines[5]}" == checkout_target_rev=* \
      && "${lines[6]}" == lean_report_required=* ]] || return 1

  generation="${lines[0]#generation=}"
  created_at="${lines[1]#created_at=}"
  previous_revision="${lines[2]#previous_platform_rev=}"
  target_revision="${lines[3]#target_platform_rev=}"
  checkout_previous_revision="${lines[4]#checkout_previous_rev=}"
  checkout_target_revision="${lines[5]#checkout_target_rev=}"
  lean_report_required="${lines[6]#lean_report_required=}"
  now="$(date -u +%s 2>/dev/null)" || return 1
  [[ "$generation" =~ ^[0-9]+-[0-9]+-[0-9]+$ ]] || return 1
  timestamp_is_usable "$created_at" "$now" || return 1
  if [[ "$previous_revision" == "none" ]]; then
    [[ "$target_revision" == "none" ]] || return 1
  else
    [[ "$previous_revision" =~ ^[0-9a-f]{40}$ \
        && "$target_revision" =~ ^[0-9a-f]{40}$ ]] || return 1
  fi
  [[ "$lean_report_required" == "0" || "$lean_report_required" == "1" ]] \
    || return 1
  if [[ "$checkout_previous_revision" == "none" ]]; then
    [[ "$checkout_target_revision" == "none" \
        && "$lean_report_required" == "0" ]] || return 1
  else
    [[ "$checkout_previous_revision" =~ ^[0-9a-f]{40}$ \
        && "$checkout_target_revision" =~ ^[0-9a-f]{40}$ ]] || return 1
  fi

  RESTART_OBLIGATION_GENERATION="$generation"
  RESTART_OBLIGATION_CREATED_AT="$created_at"
  RESTART_OBLIGATION_PREVIOUS_REV="$previous_revision"
  RESTART_OBLIGATION_TARGET_REV="$target_revision"
  RESTART_OBLIGATION_CHECKOUT_PREVIOUS_REV="$checkout_previous_revision"
  RESTART_OBLIGATION_CHECKOUT_TARGET_REV="$checkout_target_revision"
  RESTART_OBLIGATION_LEAN_REPORT_REQUIRED="$lean_report_required"
}

persist_restart_obligation() {
  local state="$1" generation="$2" created_at="$3"
  local previous_revision="$4" target_revision="$5"
  local checkout_previous_revision="$6" checkout_target_revision="$7"
  local lean_report_required="$8" temporary
  temporary="${state}.next-${generation}-$RANDOM"
  if ! (set -o noclobber; {
      printf 'generation=%s\n' "$generation"
      printf 'created_at=%s\n' "$created_at"
      printf 'previous_platform_rev=%s\n' "$previous_revision"
      printf 'target_platform_rev=%s\n' "$target_revision"
      printf 'checkout_previous_rev=%s\n' "$checkout_previous_revision"
      printf 'checkout_target_rev=%s\n' "$checkout_target_revision"
      printf 'lean_report_required=%s\n' "$lean_report_required"
    } > "$temporary") 2>/dev/null \
      || ! mv "$temporary" "$state"; then
    rm -f -- "$temporary" 2>/dev/null || true
    return 1
  fi
}

record_restart_obligation() {
  local previous_revision="$1" target_revision="$2" reason="$3"
  local checkout_previous_revision="${4:-}" checkout_target_revision="${5:-}"
  local lean_report_required="${6:-0}"
  local state now generation existing_generation existing_previous existing_target
  local existing_checkout_previous existing_checkout_target existing_lean_report_required
  state="$(restart_activation_state_path)"
  [[ -d "$(dirname -- "$state")" ]] || {
    say "RESTART-OBLIGATION WRITE-FAIL: state directory unavailable; refusing $reason"
    return 1
  }
  if ! restart_state_lock_acquire "$state"; then
    say "RESTART-OBLIGATION WRITE-FAIL: state locked; refusing $reason"
    return 1
  fi

  if [[ -e "$state" ]]; then
    if ! load_restart_obligation "$state"; then
      restart_state_lock_release 2>/dev/null || true
      say "RESTART-OBLIGATION WRITE-FAIL: existing state invalid; refusing $reason"
      return 1
    fi
    existing_previous="$RESTART_OBLIGATION_PREVIOUS_REV"
    existing_target="$RESTART_OBLIGATION_TARGET_REV"
    existing_checkout_previous="$RESTART_OBLIGATION_CHECKOUT_PREVIOUS_REV"
    existing_checkout_target="$RESTART_OBLIGATION_CHECKOUT_TARGET_REV"
    existing_lean_report_required="$RESTART_OBLIGATION_LEAN_REPORT_REQUIRED"
    existing_generation="$RESTART_OBLIGATION_GENERATION"
    if [[ "$existing_previous" != "none" ]]; then
      previous_revision="$existing_previous"
      [[ -n "$target_revision" ]] || target_revision="$existing_target"
    fi
    if [[ "$existing_checkout_previous" != "none" ]]; then
      checkout_previous_revision="$existing_checkout_previous"
      [[ -n "$checkout_target_revision" ]] \
        || checkout_target_revision="$existing_checkout_target"
    fi
    if [[ "$existing_lean_report_required" == "1" ]]; then
      lean_report_required=1
    fi
  fi

  [[ -n "$previous_revision" ]] || previous_revision="none"
  [[ -n "$target_revision" ]] || target_revision="none"
  if [[ "$previous_revision" == "none" ]]; then
    if [[ "$target_revision" != "none" ]]; then
      restart_state_lock_release 2>/dev/null || true
      say "RESTART-OBLIGATION WRITE-FAIL: missing rollback origin; refusing $reason"
      return 1
    fi
  elif [[ ! "$previous_revision" =~ ^[0-9a-f]{40}$ \
      || ! "$target_revision" =~ ^[0-9a-f]{40}$ ]]; then
    restart_state_lock_release 2>/dev/null || true
    say "RESTART-OBLIGATION WRITE-FAIL: invalid revisions; refusing $reason"
    return 1
  fi
  [[ -n "$checkout_previous_revision" ]] || checkout_previous_revision="none"
  [[ -n "$checkout_target_revision" ]] || checkout_target_revision="none"
  if [[ "$lean_report_required" != "0" && "$lean_report_required" != "1" ]]; then
    restart_state_lock_release 2>/dev/null || true
    say "RESTART-OBLIGATION WRITE-FAIL: invalid Lean report flag; refusing $reason"
    return 1
  fi
  if [[ "$checkout_previous_revision" == "none" ]]; then
    if [[ "$checkout_target_revision" != "none" \
        || "$lean_report_required" != "0" ]]; then
      restart_state_lock_release 2>/dev/null || true
      say "RESTART-OBLIGATION WRITE-FAIL: missing checkout origin; refusing $reason"
      return 1
    fi
  elif [[ ! "$checkout_previous_revision" =~ ^[0-9a-f]{40}$ \
      || ! "$checkout_target_revision" =~ ^[0-9a-f]{40}$ ]]; then
    restart_state_lock_release 2>/dev/null || true
    say "RESTART-OBLIGATION WRITE-FAIL: invalid checkout revisions; refusing $reason"
    return 1
  fi

  now="$(date -u +%s 2>/dev/null)" || now=""
  if ! timestamp_is_usable "$now" "$now"; then
    restart_state_lock_release 2>/dev/null || true
    say "RESTART-OBLIGATION WRITE-FAIL: unusable clock; refusing $reason"
    return 1
  fi
  generation="${now}-$$-${RANDOM}"
  while [[ "$generation" == "${existing_generation:-}" ]]; do
    generation="${now}-$$-${RANDOM}"
  done
  if ! persist_restart_obligation \
      "$state" "$generation" "$now" \
      "$previous_revision" "$target_revision" \
      "$checkout_previous_revision" "$checkout_target_revision" \
      "$lean_report_required"; then
    restart_state_lock_release 2>/dev/null || true
    say "RESTART-OBLIGATION WRITE-FAIL: persistence failed; refusing $reason"
    return 1
  fi
  ACTIVATION_ROLLBACK_REV="$([[ "$previous_revision" == "none" ]] \
    || printf '%s' "$previous_revision")"
  if ! restart_state_lock_release; then
    say "RESTART-OBLIGATION RETAINED: generation $generation durable but state lock remained"
    return 1
  fi
  say "RESTART-OBLIGATION RECORDED: generation $generation before $reason"
}

clear_lean_report_requirement() {
  local state="$1" verified_generation="$2" current_generation
  if ! restart_state_lock_acquire "$state"; then
    say "LEAN-REPORT-OBLIGATION RETAINED: generation $verified_generation; state locked"
    return 1
  fi
  if ! load_restart_obligation "$state"; then
    restart_state_lock_release 2>/dev/null || true
    say "LEAN-REPORT-OBLIGATION RETAINED: generation $verified_generation changed to invalid state"
    return 1
  fi
  current_generation="$RESTART_OBLIGATION_GENERATION"
  if [[ "$current_generation" != "$verified_generation" ]]; then
    restart_state_lock_release 2>/dev/null || true
    say "LEAN-REPORT-OBLIGATION RETAINED: newer generation $current_generation superseded generation $verified_generation"
    return 1
  fi
  if ! persist_restart_obligation \
      "$state" "$current_generation" "$RESTART_OBLIGATION_CREATED_AT" \
      "$RESTART_OBLIGATION_PREVIOUS_REV" "$RESTART_OBLIGATION_TARGET_REV" \
      "$RESTART_OBLIGATION_CHECKOUT_PREVIOUS_REV" \
      "$RESTART_OBLIGATION_CHECKOUT_TARGET_REV" 0; then
    restart_state_lock_release 2>/dev/null || true
    say "LEAN-REPORT-OBLIGATION RETAINED: generation $verified_generation could not be persisted"
    return 1
  fi
  if ! restart_state_lock_release; then
    say "LEAN-REPORT-OBLIGATION RETAINED: generation $verified_generation but state lock remained"
    return 1
  fi
}

resolve_lean_report_make_bin() {
  local make_bin="${FKST_MAKE_BIN:-}"
  if [[ -z "$make_bin" ]]; then
    make_bin="$(command -v make 2>/dev/null)" || make_bin=""
  fi
  printf '%s\n' "$make_bin"
  [[ "$make_bin" == /* && -f "$make_bin" && -x "$make_bin" ]]
}

reconcile_lean_report_obligation() {
  local state="$1" verified_generation="$2" make_bin=""
  local rebuild_rc checkout_head
  checkout_head="$(git -C "$FKST_HOST_ROOT" rev-parse HEAD 2>/dev/null)" || checkout_head=""
  if [[ ! "$checkout_head" =~ ^[0-9a-f]{40}$ ]]; then
    say "LEAN-REPORT-REBUILD FAIL: deployed checkout HEAD is unreadable; obligation retained"
    return 1
  fi
  if [[ "$checkout_head" == "$RESTART_OBLIGATION_CHECKOUT_PREVIOUS_REV" ]]; then
    if ! clear_lean_report_requirement "$state" "$verified_generation"; then
      return 1
    fi
    say "LEAN-REPORT-REBUILD NOT REQUIRED: generation $verified_generation target not deployed"
    return 0
  fi
  if [[ "$checkout_head" != "$RESTART_OBLIGATION_CHECKOUT_TARGET_REV" ]] \
      && ! git -C "$FKST_HOST_ROOT" merge-base --is-ancestor \
        "$RESTART_OBLIGATION_CHECKOUT_TARGET_REV" "$checkout_head" >/dev/null 2>&1; then
    say "LEAN-REPORT-REBUILD FAIL: deployed checkout HEAD ${checkout_head:0:12} does not reconcile with generation $verified_generation; obligation retained"
    return 1
  fi
  if ! make_bin="$(resolve_lean_report_make_bin)"; then
    say "LEAN-REPORT-REBUILD FAIL: make is not an executable absolute path: ${make_bin:-missing}"
    return 1
  fi

  say "LEAN-REPORT-REBUILD REQUIRED: generation $verified_generation checkout ${RESTART_OBLIGATION_CHECKOUT_PREVIOUS_REV:0:12}->${RESTART_OBLIGATION_CHECKOUT_TARGET_REV:0:12}"
  if "$make_bin" -C "$FKST_HOST_ROOT" lean-report; then
    if ! clear_lean_report_requirement "$state" "$verified_generation"; then
      return 1
    fi
    LEAN_REPORT_REBUILT_THIS_CYCLE=1
    say "LEAN-REPORT-REBUILD OK: generation $verified_generation"
    return 0
  else
    rebuild_rc=$?
  fi
  say "LEAN-REPORT-REBUILD FAIL: generation $verified_generation make lean-report exit $rebuild_rc; obligation retained"
  return 1
}

ensure_restart_defer_state() {
  local state="$1" now="$2" temporary
  [[ -e "$state" ]] && { [[ -f "$state" ]]; return; }
  temporary="${state}.next-$$-$RANDOM"
  printf '%s\n' "$now" > "$temporary" 2>/dev/null || return 1
  if ! ln "$temporary" "$state" 2>/dev/null && [[ ! -f "$state" ]]; then
    rm -f -- "$temporary"
    return 1
  fi
  rm -f -- "$temporary"
}

defer_restart_with_bound() {
  local state="$1" alive="$2" leases="$3" now started bound elapsed extra
  now="$(date -u +%s 2>/dev/null)" || now=""
  if ! timestamp_is_usable "$now" "$now"; then
    say "RESTART-DEFER INVALID: clock unavailable; forcing restart"
    return 1
  fi
  if ! ensure_restart_defer_state "$state" "$now"; then
    say "RESTART-DEFER INVALID: state unavailable; forcing restart"
    return 1
  fi
  IFS= read -r started < "$state" 2>/dev/null || started=""
  IFS= read -r extra < <(sed -n '2p' "$state" 2>/dev/null) || extra=""
  if [[ -n "$extra" ]] || ! timestamp_is_usable "$started" "$now"; then
    say "RESTART-DEFER INVALID: started=${started:-missing}; forcing restart"
    return 1
  fi

  bound="$(restart_defer_bound_seconds)"
  elapsed=$((10#$now - 10#$started))
  if [[ "$elapsed" -ge "$bound" ]]; then
    say "FORCE-RESTART: defer bound exceeded (elapsed=${elapsed}s bound=${bound}s leases=$leases); draining and restarting"
    return 1
  fi
  say "DEFER-RESTART: $leases live implement lease(s) + engine alive (pid $alive); deferred ${elapsed}s of ${bound}s bound"
  return 0
}

clear_restart_obligation() {
  local state="$1" defer_state="$2" verified_generation="$3" current_generation
  if ! restart_state_lock_acquire "$state"; then
    say "RESTART-OBLIGATION RETAINED: verified generation $verified_generation; state locked"
    return 1
  fi
  if ! load_restart_obligation "$state"; then
    restart_state_lock_release 2>/dev/null || true
    say "RESTART-OBLIGATION RETAINED: verified generation $verified_generation changed to invalid state"
    return 1
  fi
  current_generation="$RESTART_OBLIGATION_GENERATION"
  if [[ "$current_generation" != "$verified_generation" ]]; then
    restart_state_lock_release 2>/dev/null || true
    say "RESTART-OBLIGATION RETAINED: newer generation $current_generation superseded verified generation $verified_generation"
    return 0
  fi
  if ! rm -f -- "$state" \
      || [[ -e "$state" ]]; then
    restart_state_lock_release 2>/dev/null || true
    say "RESTART-OBLIGATION RETAINED: verified generation $verified_generation could not be cleared"
    return 1
  fi
  if ! rm -f -- "$defer_state"; then
    restart_state_lock_release 2>/dev/null || true
    say "RESTART-OBLIGATION CLEAR-DEFER-FAIL: generation $verified_generation cleared but defer evidence remained"
    return 1
  fi
  if ! restart_state_lock_release; then
    say "RESTART-OBLIGATION CLEAR-LOCK-FAIL: generation $verified_generation cleared but lock remained"
    return 1
  fi
  say "RESTART-OBLIGATION CLEARED: verified generation $verified_generation with new pid and launchd service"
}

restart_if_needed() {
  local state defer_state alive leases verified_generation
  state="$(restart_activation_state_path)"
  defer_state="$(restart_defer_state_path)"

  if [[ "$CHANGED" == "1" && ! -e "$state" ]]; then
    say "RESTART-OBLIGATION MISSING: changed state lacked write-ahead journal; recovering"
    if ! record_restart_obligation \
        "${PLATFORM_CURRENT_REV:-}" "${PLATFORM_DEV_REV:-}" \
        "post-mutation recovery"; then
      say "RESTART-OBLIGATION UNRECORDED: forcing immediate restart"
      restart_engine
      return
    fi
  fi
  if [[ ! -e "$state" && -e "$defer_state" ]]; then
    say "RESTART-OBLIGATION RECOVERING: orphaned defer state requires reconciliation"
    if ! record_restart_obligation "" "" "orphaned defer-state recovery"; then
      say "RESTART-OBLIGATION RETAINED: orphaned defer state could not be journaled; forcing restart"
      restart_engine
      return
    fi
  fi
  if [[ ! -e "$state" ]]; then
    say "ALL CURRENT; no restart"
    return 0
  fi

  if load_restart_obligation "$state"; then
    verified_generation="$RESTART_OBLIGATION_GENERATION"
    if [[ "$RESTART_OBLIGATION_PREVIOUS_REV" == "none" ]]; then
      ACTIVATION_ROLLBACK_REV=""
    else
      ACTIVATION_ROLLBACK_REV="$RESTART_OBLIGATION_PREVIOUS_REV"
      PLATFORM_CURRENT_REV="$RESTART_OBLIGATION_PREVIOUS_REV"
      PLATFORM_DEV_REV="$RESTART_OBLIGATION_TARGET_REV"
    fi
    if [[ "$RESTART_OBLIGATION_LEAN_REPORT_REQUIRED" == "1" ]]; then
      if ! reconcile_lean_report_obligation "$state" "$verified_generation"; then
        say "RESTART-OBLIGATION RETAINED: Lean report rebuild failed for generation $verified_generation"
        return 1
      fi
    fi
  else
    verified_generation="invalid"
    ACTIVATION_ROLLBACK_REV=""
    say "RESTART-OBLIGATION INVALID: state retained; forcing restart"
  fi
  if [[ "$CHANGED" == "0" ]]; then
    say "RESTART-OBLIGATION PENDING: retrying generation $verified_generation on current pins"
  fi

  alive="$(engine_pid)"
  if [[ "$verified_generation" != "invalid" && -n "$alive" ]]; then
    leases="$(implement_lease_count)"
    if [[ "$leases" -gt 0 ]]; then
      defer_restart_with_bound "$defer_state" "$alive" "$leases" && return 0
    fi
  fi

  say "RESTART-OBLIGATION RECONCILING: generation $verified_generation"
  if restart_engine; then
    if [[ "$verified_generation" == "invalid" ]]; then
      say "RESTART-OBLIGATION RETAINED: restart verified but generation is invalid"
      return 1
    fi
    clear_restart_obligation "$state" "$defer_state" "$verified_generation"
    return
  fi
  say "RESTART-OBLIGATION RETAINED: restart failed for generation $verified_generation"
  return 1
}
