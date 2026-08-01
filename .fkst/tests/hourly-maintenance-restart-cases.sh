# Restart-policy cases sourced by hourly-maintenance-behavior.sh.

create_restart_control_fixture() {
  local root="$1"
  export FKST_RUN_SCRIPT="$root/bin/run-engine"
  export FKST_LAUNCHD_LABEL="com.example.synthetic-fkst"
  export RUN_CALLS_FILE="$root/run.calls"
  export SLEEP_CALLS_FILE="$root/sleep.calls"
  cat > "$FKST_RUN_SCRIPT" <<'SH'
#!/usr/bin/env bash
printf '%s\n' "$*" >> "$RUN_CALLS_FILE"
exit "${RUN_EXIT_CODE:-0}"
SH
  cat > "$root/bin/sleep" <<'SH'
#!/usr/bin/env bash
printf '%s\n' "$1" >> "$SLEEP_CALLS_FILE"
SH
  chmod +x "$FKST_RUN_SCRIPT" "$root/bin/sleep"
  export PATH="$root/bin:/usr/bin:/bin"
}

write_pending_activation_fixture() {
  local path="$1" generation="$2" created_at="$3" previous_rev="$4" target_rev="$5"
  {
    printf 'generation=%s\n' "$generation"
    printf 'created_at=%s\n' "$created_at"
    printf 'previous_platform_rev=%s\n' "$previous_rev"
    printf 'target_platform_rev=%s\n' "$target_rev"
  } > "$path"
}

local_implement_work_controls_pending_restart() (
  load_implementation || exit 1
  local root implement_pid pending_state defer_state supervisor_log
  root="$(mktemp -d -t hourly-maintenance-defer.XXXXXX)" || exit 1
  implement_pid=""
  trap '[[ -z "${implement_pid:-}" ]] || kill "$implement_pid" 2>/dev/null || true; [[ -z "${implement_pid:-}" ]] || wait "$implement_pid" 2>/dev/null || true; rm -rf "$root"' EXIT
  mkdir -p "$root/bin" "$root/checkout" "$root/logs" "$root/runtime/logs"
  export FKST_HOST_ROOT="$root/checkout"
  export FKST_MAINTENANCE_LOG="$root/logs/hourly-maintenance.log"
  export FKST_RUNTIME_ROOT="$root/runtime"
  export FKST_GITHUB_REPO="example/synthetic"
  export FKST_DEVLOOP_MANAGED_BOT_LOGINS="ElonSG"
  export FKST_CODEX_TIMEOUT_IMPLEMENT=10800
  export FKST_RESTART_TIMEOUT_SECONDS=2
  export FKST_RESTART_POLL_SECONDS=1
  export FKST_RUN_SCRIPT="$root/bin/run-engine"
  export FKST_LAUNCHD_LABEL="com.example.synthetic-fkst"
  export RESTART_STOPPED_FILE="$root/restart.stopped"
  cat > "$FKST_RUN_SCRIPT" <<SH
#!/usr/bin/env bash
printf '%s\n' "\$*" >> "$root/run.calls"
touch "$RESTART_STOPPED_FILE"
SH
  cat > "$root/bin/pgrep" <<'SH'
#!/usr/bin/env bash
if [[ -e "$RESTART_STOPPED_FILE" ]]; then
  printf '5252\n'
else
  printf '4242\n'
fi
SH
  cat > "$root/bin/gh" <<'SH'
#!/usr/bin/env bash
printf '3\n'
SH
  cat > "$root/bin/sleep" <<'SH'
#!/usr/bin/env bash
exit 0
SH
  cat > "$root/bin/launchctl" <<'SH'
#!/usr/bin/env bash
printf '4242 0 com.example.synthetic-fkst\n'
SH
  chmod +x "$FKST_RUN_SCRIPT" "$root/bin/pgrep" "$root/bin/gh" \
    "$root/bin/sleep" "$root/bin/launchctl"
  export PATH="$root/bin:/usr/bin:/bin"
  pending_state="$FKST_RUNTIME_ROOT/hourly-maintenance.pending-activation"
  defer_state="$FKST_RUNTIME_ROOT/hourly-maintenance.restart-defer-since"
  supervisor_log="$FKST_RUNTIME_ROOT/logs/supervisor-1-4242.log"

  /bin/sleep 300 &
  implement_pid=$!
  printf 'event=dept_child_spawn dept=github-devloop.implement pid=%s exit_code=pending\n' \
    "$implement_pid" > "$supervisor_log"
  record_pending_activation "" "" "synthetic local implement activation" \
    || fail "could not create the activation obligation"
  CHANGED=1

  restart_if_needed || fail "restart deferral should exit successfully"
  [[ ! -e "$root/run.calls" ]] || fail "engine control ran during DEFER-RESTART"
  [[ -f "$pending_state" ]] || fail "deferral did not persist the activation obligation"
  [[ -f "$defer_state" ]] || fail "deferral did not persist its bounded age"
  command grep -q 'DEFER-RESTART: 1 local implement child process(es) active' \
    "$FKST_MAINTENANCE_LOG" || fail "local implement deferral was not reported"

  kill "$implement_pid"
  wait "$implement_pid" 2>/dev/null || true
  implement_pid=""
  : > "$FKST_MAINTENANCE_LOG"
  CHANGED=0
  restart_if_needed || fail "pending activation was not retried on the next current-pin cycle"
  [[ -e "$root/run.calls" ]] || fail "pending activation did not restart after local work cleared"
  [[ ! -e "$pending_state" ]] || fail "verified restart did not clear the activation obligation"
  [[ ! -e "$defer_state" ]] || fail "verified restart did not clear the defer age"
  ! command grep -q 'DEFER-RESTART' "$FKST_MAINTENANCE_LOG" \
    || fail "foreign-host implementing labels deferred a host with no local implement child"

  rm -f "$RESTART_STOPPED_FILE" "$root/run.calls"
  : > "$FKST_MAINTENANCE_LOG"
  /bin/sleep 300 &
  implement_pid=$!
  printf 'event=dept_child_spawn dept=github-devloop.implement pid=%s exit_code=pending\n' \
    "$implement_pid" > "$supervisor_log"
  record_pending_activation "" "" "second synthetic local implement activation" \
    || fail "could not create the second activation obligation"
  CHANGED=1
  restart_if_needed || fail "fresh local implement work should defer restart"
  printf '1\n' > "$defer_state"
  : > "$FKST_MAINTENANCE_LOG"
  CHANGED=0
  restart_if_needed || fail "expired pending activation should force restart"
  [[ -e "$root/run.calls" ]] || fail "bounded defer did not force restart"
  command grep -q 'FORCE-RESTART: defer bound reached' "$FKST_MAINTENANCE_LOG" \
    || fail "bounded defer transition was not reported"
)

deferred_activation_retains_platform_rollback_origin() (
  load_implementation || exit 1
  local root pending_state
  root="$(mktemp -d -t hourly-maintenance-deferred-rollback.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  create_platform_fixture "$root" || exit 1
  create_checkout_files "$root" || exit 1
  mkdir -p "$root/runtime"
  export FKST_RUNTIME_ROOT="$root/runtime"
  FRAMEWORK_CALLS_FILE="$root/framework.calls"
  export FRAMEWORK_CALLS_FILE
  write_framework_stub success
  export_platform_environment
  export FKST_CODEX_TIMEOUT_IMPLEMENT=10800
  export FKST_RESTART_TIMEOUT_SECONDS=1
  export FKST_RESTART_POLL_SECONDS=1
  export FKST_RUN_SCRIPT="$root/bin/run-engine"
  export FKST_LAUNCHD_LABEL="com.example.synthetic-fkst"
  cat > "$FKST_RUN_SCRIPT" <<'SH'
#!/usr/bin/env bash
exit 0
SH
  cat > "$root/bin/sleep" <<'SH'
#!/usr/bin/env bash
exit 0
SH
  chmod +x "$FKST_RUN_SCRIPT" "$root/bin/sleep"
  export PATH="$root/bin:/usr/bin:/bin"
  pending_state="$FKST_RUNTIME_ROOT/hourly-maintenance.pending-activation"

  sync_platform || fail "platform activation setup should succeed"
  engine_pid() { printf '4242\n'; }
  active_local_implement_count() { printf '1\n'; }
  restart_if_needed || fail "cycle 1 should defer the pending platform activation"
  command grep -q "$NEW_PLATFORM_REV" "$CHECKOUT_ROOT/fkst.workspace.toml" \
    || fail "cycle 1 did not leave the new revision pending activation"

  # A later cycle reads the new pin as current and has none of cycle 1's globals.
  CHANGED=0
  PLATFORM_CURRENT_REV="$NEW_PLATFORM_REV"
  ACTIVATION_ROLLBACK_REV=""
  engine_pid() { return 1; }
  launchd_service_state() { printf 'not-in-service\n'; }
  restart_if_needed && fail "confirmed startup failure should fail after rollback"

  command grep -q "$OLD_PLATFORM_REV" "$CHECKOUT_ROOT/fkst.workspace.toml" \
    || fail "deferred activation did not roll back to its durable known-good revision"
  command grep -q 'lock-mutated-by-host-lock-2' "$CHECKOUT_ROOT/fkst.lock" \
    || fail "deferred rollback did not regenerate the known-good lock"
  [[ -f "$pending_state" ]] \
    || fail "failed activation dropped its durable obligation"
)

verified_restart_cannot_clear_newer_activation_generation() (
  load_implementation || exit 1
  local root pending_state now
  root="$(mktemp -d -t hourly-maintenance-generation-fence.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  mkdir -p "$root/runtime" "$root/logs"
  export FKST_RUNTIME_ROOT="$root/runtime"
  export FKST_MAINTENANCE_LOG="$root/logs/hourly-maintenance.log"
  pending_state="$FKST_RUNTIME_ROOT/hourly-maintenance.pending-activation"
  now="$(date -u +%s)"
  write_pending_activation_fixture "$pending_state" "${now}-1-1" "$now" none none
  CHANGED=0
  engine_pid() { return 1; }
  restart_engine() {
    write_pending_activation_fixture \
      "$pending_state" "${now}-2-2" "$now" none none
    return 0
  }

  restart_if_needed || fail "older generation reconciliation should remain successful"
  [[ -f "$pending_state" ]] \
    || fail "verified restart erased a newer activation generation"
  command grep -q "^generation=${now}-2-2$" "$pending_state" \
    || fail "older reconciler did not preserve the newer generation"
  command grep -q 'ACTIVATION-RETAINED: verified generation .* was superseded by' \
    "$FKST_MAINTENANCE_LOG" \
    || fail "generation-fence retention was not reported"
)

unusable_defer_timestamp_forces_restart() (
  local unusable_timestamp="$1"
  load_implementation || exit 1
  local root pending_state defer_state now
  root="$(mktemp -d -t hourly-maintenance-invalid-defer.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  mkdir -p "$root/runtime" "$root/logs"
  export FKST_RUNTIME_ROOT="$root/runtime"
  export FKST_MAINTENANCE_LOG="$root/logs/hourly-maintenance.log"
  export FKST_CODEX_TIMEOUT_IMPLEMENT=10800
  pending_state="$FKST_RUNTIME_ROOT/hourly-maintenance.pending-activation"
  defer_state="$FKST_RUNTIME_ROOT/hourly-maintenance.restart-defer-since"
  now="$(date -u +%s)"
  write_pending_activation_fixture "$pending_state" "${now}-1-1" "$now" none none
  printf '%s\n' "$unusable_timestamp" > "$defer_state"
  CHANGED=0
  engine_pid() { printf '4242\n'; }
  active_local_implement_count() { printf '1\n'; }
  restart_engine() { printf 'verified restart\n' > "$root/restart.calls"; }

  restart_if_needed \
    || fail "unusable defer timestamp $unusable_timestamp aborted reconciliation"
  [[ -f "$root/restart.calls" ]] \
    || fail "unusable defer timestamp $unusable_timestamp allowed unbounded deferral"
  command grep -q 'FORCE-RESTART: invalid defer state' "$FKST_MAINTENANCE_LOG" \
    || fail "unusable defer timestamp $unusable_timestamp was not reported"
)

octal_defer_timestamp_forces_restart() (
  unusable_defer_timestamp_forces_restart 08
)

overflowing_defer_timestamp_forces_restart() (
  unusable_defer_timestamp_forces_restart 9223372036854775808
)

failed_restart_retains_pending_activation() (
  load_implementation || exit 1
  local root pending_state
  root="$(mktemp -d -t hourly-maintenance-pending-failure.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  mkdir -p "$root/runtime" "$root/logs"
  export FKST_RUNTIME_ROOT="$root/runtime"
  export FKST_MAINTENANCE_LOG="$root/logs/hourly-maintenance.log"
  pending_state="$FKST_RUNTIME_ROOT/hourly-maintenance.pending-activation"
  record_pending_activation "" "" "synthetic failed activation" \
    || fail "could not create the failed activation obligation"
  CHANGED=1
  engine_pid() { return 1; }
  restart_engine() { say "synthetic restart failure"; return 1; }

  restart_if_needed && fail "failed restart must fail the maintenance cycle"
  [[ -f "$pending_state" ]] || fail "restart failure dropped the activation obligation"
  command grep -q 'ACTIVATION-PENDING: recorded' "$FKST_MAINTENANCE_LOG" \
    || fail "activation obligation creation was not logged"
  command grep -q 'ACTIVATION-RETAINED: restart failed' "$FKST_MAINTENANCE_LOG" \
    || fail "activation obligation retention was not logged"
)

orphaned_defer_state_is_not_dropped() (
  load_implementation || exit 1
  local root defer_state
  root="$(mktemp -d -t hourly-maintenance-orphaned-defer.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  mkdir -p "$root/runtime" "$root/logs"
  export FKST_RUNTIME_ROOT="$root/runtime"
  export FKST_MAINTENANCE_LOG="$root/logs/hourly-maintenance.log"
  defer_state="$FKST_RUNTIME_ROOT/hourly-maintenance.restart-defer-since"
  printf '%s\n' "$(date -u +%s)" > "$defer_state"
  CHANGED=0
  engine_pid() { return 1; }
  restart_engine() { printf 'verified restart\n' > "$root/restart.calls"; }

  restart_if_needed || fail "orphaned defer evidence should force a verified restart"
  [[ -f "$root/restart.calls" ]] || fail "orphaned defer evidence was dropped without restart"
  command grep -q 'ACTIVATION-PENDING-RECOVERED: defer state existed without its obligation marker' \
    "$FKST_MAINTENANCE_LOG" || fail "orphaned defer recovery was not logged"
)

late_engine_pid_is_accepted_before_restart_budget_expires() (
  load_implementation || exit 1
  local root waited=0 slept
  root="$(mktemp -d -t hourly-maintenance-restart-late.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  mkdir -p "$root/bin" "$root/checkout" "$root/logs"
  export FKST_HOST_ROOT="$root/checkout"
  export FKST_MAINTENANCE_LOG="$root/logs/hourly-maintenance.log"
  export PGREP_CALLS_FILE="$root/pgrep.calls"
  create_restart_control_fixture "$root"
  cat > "$root/bin/pgrep" <<'SH'
#!/usr/bin/env bash
count=0
[[ ! -f "$PGREP_CALLS_FILE" ]] || count="$(<"$PGREP_CALLS_FILE")"
count=$((count + 1))
printf '%s\n' "$count" > "$PGREP_CALLS_FILE"
[[ "$count" -ge 4 ]] && printf '5252\n'
SH
  cat > "$root/bin/launchctl" <<'SH'
#!/usr/bin/env bash
printf '5252 0 com.example.synthetic-fkst\n'
SH
  chmod +x "$root/bin/pgrep" "$root/bin/launchctl"
  export FKST_RESTART_TIMEOUT_SECONDS=10
  export FKST_RESTART_POLL_SECONDS=2
  PLATFORM_DEV_REV=2222222222222222222222222222222222222222
  CHECKOUT_DEV_REV=3333333333333333333333333333333333333333

  restart_engine || fail "late engine PID was rejected before the restart budget expired"
  while IFS= read -r slept; do
    waited=$((waited + slept))
  done < "$SLEEP_CALLS_FILE"
  [[ "$waited" == "4" ]] \
    || fail "conditional restart wait did not stop after the late PID appeared: waited=$waited"
  [[ "$waited" -lt "$FKST_RESTART_TIMEOUT_SECONDS" ]] \
    || fail "healthy restart consumed the full restart budget"
  command grep -q 'SYNCED OK (engine pid 5252' "$FKST_MAINTENANCE_LOG" \
    || fail "late healthy PID was not reported"
  ! command grep -q 'ROLLBACK' "$FKST_MAINTENANCE_LOG" \
    || fail "late healthy PID triggered platform rollback"
)

restart_timeout_with_launchd_in_service_does_not_roll_back_platform() (
  load_implementation || exit 1
  local root
  root="$(mktemp -d -t hourly-maintenance-restart-timeout.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  create_platform_fixture "$root" || exit 1
  create_checkout_files "$root" || exit 1
  FRAMEWORK_CALLS_FILE="$root/framework.calls"
  export FRAMEWORK_CALLS_FILE
  write_framework_stub success
  export_platform_environment
  create_restart_control_fixture "$root"
  cat > "$root/bin/pgrep" <<'SH'
#!/usr/bin/env bash
exit 1
SH
  cat > "$root/bin/launchctl" <<'SH'
#!/usr/bin/env bash
printf -- '- 0 com.example.synthetic-fkst\n'
SH
  chmod +x "$root/bin/pgrep" "$root/bin/launchctl"
  export FKST_RESTART_TIMEOUT_SECONDS=6
  export FKST_RESTART_POLL_SECONDS=2

  sync_platform || fail "platform sync setup should succeed"
  command cp "$CHECKOUT_ROOT/fkst.workspace.toml" "$root/workspace.after-sync"
  command cp "$CHECKOUT_ROOT/fkst.lock" "$root/lock.after-sync"
  restart_engine && fail "missing PID at the restart deadline must be unhealthy"
  command cmp -s "$root/workspace.after-sync" "$CHECKOUT_ROOT/fkst.workspace.toml" \
    || fail "deadline expiry rolled back the platform without confirmed startup failure"
  command cmp -s "$root/lock.after-sync" "$CHECKOUT_ROOT/fkst.lock" \
    || fail "deadline expiry rolled back the lock without confirmed startup failure"
  command grep -q \
    'UNHEALTHY after restart (state=waiting-for-new-pid waited=6s budget=6s launchd=in-service old_pid=none last_pid=none)' \
    "$FKST_MAINTENANCE_LOG" \
    || fail "restart timeout diagnostic omitted its wait budget or observed state"
  command grep -q 'PLATFORM-ROLLBACK-SKIPPED.*startup failure not confirmed' \
    "$FKST_MAINTENANCE_LOG" \
    || fail "unconfirmed startup failure did not explain why rollback was skipped"
)

restart_timeout_with_launchd_absent_rolls_back_platform() (
  load_implementation || exit 1
  local root
  root="$(mktemp -d -t hourly-maintenance-restart-launchd-absent.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  create_platform_fixture "$root" || exit 1
  create_checkout_files "$root" || exit 1
  FRAMEWORK_CALLS_FILE="$root/framework.calls"
  export FRAMEWORK_CALLS_FILE
  write_framework_stub success
  export_platform_environment
  create_restart_control_fixture "$root"
  cat > "$root/bin/pgrep" <<'SH'
#!/usr/bin/env bash
exit 1
SH
  cat > "$root/bin/launchctl" <<'SH'
#!/usr/bin/env bash
exit 0
SH
  chmod +x "$root/bin/pgrep" "$root/bin/launchctl"
  export FKST_RESTART_TIMEOUT_SECONDS=6
  export FKST_RESTART_POLL_SECONDS=2

  sync_platform || fail "platform sync setup should succeed"
  restart_engine && fail "missing launchd service and PID must be unhealthy"
  command grep -q "$OLD_PLATFORM_REV" "$CHECKOUT_ROOT/fkst.workspace.toml" \
    || fail "confirmed startup failure did not restore the previous platform revision"
  command grep -q 'lock-mutated-by-host-lock-2' "$CHECKOUT_ROOT/fkst.lock" \
    || fail "confirmed startup failure did not regenerate the lock from that revision"
  command grep -q \
    'UNHEALTHY after restart (state=launchd-not-in-service waited=6s budget=6s launchd=not-in-service old_pid=none last_pid=none)' \
    "$FKST_MAINTENANCE_LOG" \
    || fail "confirmed startup failure diagnostic omitted its evidence"
  command grep -q 'reverted platform to' "$FKST_MAINTENANCE_LOG" \
    || fail "confirmed startup failure did not report platform rollback"
)

unchanged_pid_remains_unhealthy_after_restart_budget() (
  load_implementation || exit 1
  local root
  root="$(mktemp -d -t hourly-maintenance-restart-old-pid.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  mkdir -p "$root/bin" "$root/checkout" "$root/logs"
  export FKST_HOST_ROOT="$root/checkout"
  export FKST_MAINTENANCE_LOG="$root/logs/hourly-maintenance.log"
  create_restart_control_fixture "$root"
  cat > "$root/bin/pgrep" <<'SH'
#!/usr/bin/env bash
printf '4242\n'
SH
  cat > "$root/bin/launchctl" <<'SH'
#!/usr/bin/env bash
printf '4242 0 com.example.synthetic-fkst\n'
SH
  chmod +x "$root/bin/pgrep" "$root/bin/launchctl"
  export FKST_RESTART_TIMEOUT_SECONDS=6
  export FKST_RESTART_POLL_SECONDS=2

  restart_engine && fail "unchanged pre-stop PID was accepted as a new engine"
  command grep -q \
    'UNHEALTHY after restart (state=old-pid-still-present waited=6s budget=6s launchd=in-service old_pid=4242 last_pid=4242)' \
    "$FKST_MAINTENANCE_LOG" \
    || fail "unchanged-PID diagnostic omitted its wait budget or observed state"
)

restart_requires_successful_stop() (
  load_implementation || exit 1
  local root
  root="$(mktemp -d -t hourly-maintenance-restart-stop.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  mkdir -p "$root/bin" "$root/checkout" "$root/logs"
  export FKST_HOST_ROOT="$root/checkout"
  export FKST_MAINTENANCE_LOG="$root/logs/hourly-maintenance.log"
  create_restart_control_fixture "$root"

  RUN_EXIT_CODE=7 restart_engine && fail "failed stop was accepted as a restart"
  return 0
)
