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
    || fail "confirmed startup failure did not restore the previous revision"
  command grep -q "lock-for-$OLD_PLATFORM_REV" "$CHECKOUT_ROOT/fkst.lock" \
    || fail "confirmed startup failure did not regenerate the previous lock"
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

missing_launchd_service_is_bootstrapped_and_logged() (
  load_implementation || exit 1
  local root launch_agents
  root="$(mktemp -d -t hourly-maintenance-launchd-reload.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  launch_agents="$root/LaunchAgents"
  mkdir -p "$root/bin" "$root/logs" "$launch_agents"
  export FKST_MAINTENANCE_LOG="$root/logs/hourly-maintenance.log"
  export FKST_LAUNCHD_LABEL="local.fkst.synthetic.supervise"
  export FKST_MAINTENANCE_LAUNCHD_LABEL="local.fkst.synthetic.maintenance"
  export FKST_LAUNCH_AGENTS_DIR="$launch_agents"
  printf 'supervise bytes\n' > "$launch_agents/$FKST_LAUNCHD_LABEL.plist"
  printf 'maintenance bytes\n' > "$launch_agents/$FKST_MAINTENANCE_LAUNCHD_LABEL.plist"
  export LAUNCHCTL_CALLS="$root/launchctl.calls"
  cat > "$root/bin/launchctl" <<'SH'
#!/usr/bin/env bash
printf '%s\n' "$*" >> "$LAUNCHCTL_CALLS"
case "$1:$2" in
  print:*/local.fkst.synthetic.maintenance) exit 0 ;;
  print:*/local.fkst.synthetic.supervise) exit 113 ;;
  bootstrap:*) exit 0 ;;
  *) exit 64 ;;
esac
SH
  chmod +x "$root/bin/launchctl"
  export PATH="$root/bin:/usr/bin:/bin"

  ensure_launchd_services || fail "missing launchd service was not recovered"
  command grep -Fq \
    "print gui/$(id -u)/local.fkst.synthetic.supervise" "$LAUNCHCTL_CALLS" \
    || fail "supervise service was not queried with launchctl print"
  command grep -Fq \
    "bootstrap gui/$(id -u) $launch_agents/local.fkst.synthetic.supervise.plist" \
    "$LAUNCHCTL_CALLS" \
    || fail "missing supervise service was not bootstrapped from LaunchAgents"
  ! command grep -Fq \
    "bootstrap gui/$(id -u) $launch_agents/local.fkst.synthetic.maintenance.plist" \
    "$LAUNCHCTL_CALLS" \
    || fail "in-service maintenance unit was bootstrapped again"
  command grep -Fq \
    "LAUNCHD-RELOAD: local.fkst.synthetic.supervise absent; bootstrap succeeded from $launch_agents/local.fkst.synthetic.supervise.plist" \
    "$FKST_MAINTENANCE_LOG" \
    || fail "successful recovery was not recorded in the maintenance log"
)

create_defer_policy_fixture() {
  local root="$1"
  mkdir -p "$root/bin" "$root/checkout" "$root/logs" "$root/slots"
  export FKST_HOST_ROOT="$root/checkout"
  export FKST_MAINTENANCE_LOG="$root/logs/hourly-maintenance.log"
  export FKST_REPORT_SLOT_ROOT="$root/slots"
  export FKST_GITHUB_REPO="example/synthetic"
  export FKST_RUN_SCRIPT="$root/bin/run-engine"
  export FKST_LAUNCHD_LABEL="com.example.synthetic-fkst"
  export GH_CALLS_FILE="$root/gh.calls"
  export FKST_RESTART_TIMEOUT_SECONDS=2
  export FKST_RESTART_POLL_SECONDS=1
  cat > "$FKST_RUN_SCRIPT" <<SH
#!/usr/bin/env bash
printf 'restart attempted\n' >> "$root/run.calls"
SH
  cat > "$root/bin/pgrep" <<'SH'
#!/usr/bin/env bash
printf '4242\n'
SH
  cat > "$root/bin/gh" <<'SH'
#!/usr/bin/env bash
printf '%s\n' "$*" >> "$GH_CALLS_FILE"
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
  CHANGED=1
}

grant_implement_lease() {
  local root="$1" owner="$2"
  mkdir -p "$root/slots/lane.lock"
  printf '%s\n' "$owner" > "$root/slots/lane.lock/owner"
}

write_activation_obligation_fixture() {
  local path="$1" generation="$2" created_at="$3"
  local previous_revision="${4:-none}" target_revision="${5:-none}"
  local checkout_previous_revision="${6:-none}" checkout_target_revision="${7:-none}"
  local lean_report_required="${8:-0}"
  {
    printf 'generation=%s\n' "$generation"
    printf 'created_at=%s\n' "$created_at"
    printf 'previous_platform_rev=%s\n' "$previous_revision"
    printf 'target_platform_rev=%s\n' "$target_revision"
    printf 'checkout_previous_rev=%s\n' "$checkout_previous_revision"
    printf 'checkout_target_rev=%s\n' "$checkout_target_revision"
    printf 'lean_report_required=%s\n' "$lean_report_required"
  } > "$path"
}

write_legacy_activation_obligation_fixture() {
  local path="$1" generation="$2" created_at="$3"
  local previous_revision="$4" target_revision="$5"
  {
    printf 'generation=%s\n' "$generation"
    printf 'created_at=%s\n' "$created_at"
    printf 'previous_platform_rev=%s\n' "$previous_revision"
    printf 'target_platform_rev=%s\n' "$target_revision"
  } > "$path"
}

legacy_activation_obligation_migrates_before_platform_pin() (
  local root obligation now legacy_generation legacy_previous
  root="$(mktemp -d -t hourly-maintenance-legacy-obligation.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  create_platform_fixture "$root" || exit 1
  create_checkout_files "$root" || exit 1
  FRAMEWORK_CALLS_FILE="$root/framework.calls"
  export FRAMEWORK_CALLS_FILE
  write_framework_stub success
  export_platform_environment
  obligation="$root/logs/restart-activation.state"
  export FKST_RESTART_ACTIVATION_STATE="$obligation"
  now="$(date +%s)"
  legacy_generation="${now}-768-1"
  legacy_previous=1111111111111111111111111111111111111111
  write_legacy_activation_obligation_fixture \
    "$obligation" "$legacy_generation" "$now" \
    "$legacy_previous" "$OLD_PLATFORM_REV"

  export FKST_RESTART_DEFER_MAX_SECONDS=3600
  export FKST_RESTART_DEFER_STATE="$root/logs/restart-defer.state"

  run_deferred_activation_cycle "$root/host.env" \
    || fail "maintenance cycle was blocked by a migrated legacy obligation"
  [[ "$(wc -l < "$obligation" | tr -d '[:space:]')" == "7" ]] \
    || fail "legacy activation obligation was not rewritten to the current schema"
  command grep -q "$NEW_PLATFORM_REV" "$CHECKOUT_ROOT/fkst.workspace.toml" \
    || fail "platform pin did not advance after legacy obligation migration"
  command grep -q "^previous_platform_rev=$legacy_previous$" "$obligation" \
    || fail "platform sync discarded the legacy obligation's rollback origin"
  command grep -q "^target_platform_rev=$NEW_PLATFORM_REV$" "$obligation" \
    || fail "platform sync did not extend the legacy obligation to the new target"
  command grep -q '^checkout_previous_rev=none$' "$obligation" \
    || fail "legacy migration did not add the neutral checkout origin"
  command grep -q '^checkout_target_rev=none$' "$obligation" \
    || fail "legacy migration did not add the neutral checkout target"
  command grep -q '^lean_report_required=0$' "$obligation" \
    || fail "legacy migration did not add the neutral Lean report flag"
  command grep -q \
    "RESTART-OBLIGATION MIGRATED: generation $legacy_generation from 4 to 7 fields" \
    "$FKST_MAINTENANCE_LOG" \
    || fail "legacy migration was not reported"
  command grep -q 'DEFER-RESTART: 1 live implement lease' \
    "$FKST_MAINTENANCE_LOG" \
    || fail "maintenance cycle did not retain the migrated obligation for restart"
)

corrupt_activation_obligation_still_refuses_platform_pin() (
  load_implementation || exit 1
  local root obligation snapshot now
  root="$(mktemp -d -t hourly-maintenance-corrupt-obligation.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  create_platform_fixture "$root" || exit 1
  create_checkout_files "$root" || exit 1
  FRAMEWORK_CALLS_FILE="$root/framework.calls"
  export FRAMEWORK_CALLS_FILE
  write_framework_stub success
  export_platform_environment
  obligation="$root/logs/restart-activation.state"
  snapshot="$root/restart-activation.before"
  export FKST_RESTART_ACTIVATION_STATE="$obligation"
  now="$(date +%s)"
  write_activation_obligation_fixture \
    "$obligation" "${now}-768-2" "$now" \
    1111111111111111111111111111111111111111 "$OLD_PLATFORM_REV" \
    none none 2
  command cp "$obligation" "$snapshot"

  load_restart_obligation "$obligation" \
    && fail "out-of-schema Lean report flag was accepted"
  sync_platform && fail "platform sync overwrote a corrupt activation obligation"
  command cmp -s "$snapshot" "$obligation" \
    || fail "corrupt activation obligation was changed instead of retained"
  command grep -q "$OLD_PLATFORM_REV" "$CHECKOUT_ROOT/fkst.workspace.toml" \
    || fail "platform pin advanced despite a corrupt activation obligation"
  command grep -q \
    'RESTART-OBLIGATION WRITE-FAIL: existing state invalid; refusing platform pin' \
    "$FKST_MAINTENANCE_LOG" \
    || fail "corrupt obligation refusal did not retain WRITE-FAIL behavior"
)

run_activation_cycle() (
  local host_config="$1"
  load_implementation || exit 1
  host_contract_load() { HOST_CONFIG="$1"; export HOST_CONFIG; }
  validate_configuration() { return 0; }
  host_contract_require() { return 0; }
  sync_checkout() { return 0; }
  sync_workspace_composition() { return 0; }
  gc_worktrees() { return 0; }
  gc_stuck_lean_builds() { return 0; }
  check_launchd_conformance() { return 0; }
  main --host-config "$host_config"
)

run_deferred_activation_cycle() (
  local host_config="$1"
  load_implementation || exit 1
  host_contract_load() { HOST_CONFIG="$1"; export HOST_CONFIG; }
  validate_configuration() { return 0; }
  host_contract_require() { return 0; }
  sync_checkout() { return 0; }
  sync_workspace_composition() { return 0; }
  gc_worktrees() { return 0; }
  gc_stuck_lean_builds() { return 0; }
  check_launchd_conformance() { return 0; }
  engine_pid() { printf '4242\n'; }
  implement_lease_count() { printf '1\n'; }
  restart_engine() { return 1; }
  main --host-config "$host_config"
)

deferred_activation_survives_a_current_second_cycle() (
  local root obligation real_mv
  root="$(mktemp -d -t hourly-maintenance-activation-cycle.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  create_platform_fixture "$root" || exit 1
  create_checkout_files "$root" || exit 1
  FRAMEWORK_CALLS_FILE="$root/framework.calls"
  export FRAMEWORK_CALLS_FILE
  write_framework_stub success
  export_platform_environment
  mkdir -p "$root/slots"
  export FKST_REPORT_SLOT_ROOT="$root/slots"
  export FKST_RESTART_DEFER_MAX_SECONDS=3600
  export FKST_RESTART_ACTIVATION_STATE="$root/logs/restart-activation.state"
  export FKST_RESTART_DEFER_STATE="$root/logs/restart-defer.state"
  obligation="$FKST_RESTART_ACTIVATION_STATE"
  create_restart_control_fixture "$root"
  grant_implement_lease "$root" "$$"

  export PGREP_CALLS_FILE="$root/pgrep.calls"
  cat > "$root/bin/pgrep" <<'SH'
#!/usr/bin/env bash
count=0
[[ ! -f "$PGREP_CALLS_FILE" ]] || count="$(<"$PGREP_CALLS_FILE")"
count=$((count + 1))
printf '%s\n' "$count" > "$PGREP_CALLS_FILE"
if [[ "$count" -lt 4 ]]; then
  printf '4242\n'
else
  printf '5252\n'
fi
SH
  cat > "$root/bin/launchctl" <<'SH'
#!/usr/bin/env bash
printf '5252 0 com.example.synthetic-fkst\n'
SH
  real_mv="$(command -v mv)"
  export REAL_MV="$real_mv"
  cat > "$root/bin/mv" <<'SH'
#!/usr/bin/env bash
target="${!#}"
if [[ "$target" == "$FKST_HOST_ROOT/fkst.workspace.toml" \
    && -s "$FKST_RESTART_ACTIVATION_STATE" ]]; then
  : > "$FKST_HOST_ROOT/obligation-observed-before-pin"
fi
exec "$REAL_MV" "$@"
SH
  chmod +x "$root/bin/pgrep" "$root/bin/launchctl" "$root/bin/mv"

  run_activation_cycle "$root/host.env" \
    || fail "first activation cycle failed"
  [[ -s "$obligation" ]] || fail "deferred cycle did not retain its activation obligation"
  command grep -q "^previous_platform_rev=$OLD_PLATFORM_REV$" "$obligation" \
    || fail "deferred obligation did not retain its rollback revision"
  command grep -q "^target_platform_rev=$NEW_PLATFORM_REV$" "$obligation" \
    || fail "deferred obligation did not retain its target revision"
  [[ -e "$root/checkout/obligation-observed-before-pin" ]] \
    || fail "activation obligation was not durable before the platform pin mutation"
  [[ ! -e "$root/run.calls" ]] || fail "first cycle restarted despite its live lease"

  rm -rf "$root/slots/lane.lock"
  run_activation_cycle "$root/host.env" \
    || fail "second activation cycle failed"
  [[ -e "$root/run.calls" ]] \
    || fail "current second cycle dropped the deferred activation instead of restarting"
  [[ ! -e "$obligation" ]] \
    || fail "verified restart did not clear its reconciled activation generation"
  command grep -q 'PLATFORM CURRENT' "$FKST_MAINTENANCE_LOG" \
    || fail "second cycle did not exercise pins-already-current behavior"
  command grep -q 'RESTART-OBLIGATION RECORDED' "$FKST_MAINTENANCE_LOG" \
    || fail "obligation creation was not reported"
  command grep -q 'RESTART-OBLIGATION CLEARED' "$FKST_MAINTENANCE_LOG" \
    || fail "obligation completion was not reported"
)

older_restart_cannot_clear_a_newer_generation() (
  load_implementation || exit 1
  local root obligation now
  root="$(mktemp -d -t hourly-maintenance-generation-clear.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  create_defer_policy_fixture "$root"
  obligation="$root/logs/restart-activation.state"
  export FKST_RESTART_ACTIVATION_STATE="$obligation"
  export FKST_RESTART_DEFER_STATE="$root/logs/restart-defer.state"
  now="$(date +%s)"
  write_activation_obligation_fixture "$obligation" "${now}-1-1" "$now"
  CHANGED=0
  restart_engine() {
    write_activation_obligation_fixture "$obligation" "${now}-2-2" "$now"
    return 0
  }

  restart_if_needed || fail "simulated verified restart should reconcile successfully"
  command grep -q "generation=${now}-2-2" "$obligation" \
    || fail "an older completing restart erased a newer activation generation"
  command grep -q 'RESTART-OBLIGATION RETAINED.*newer generation' \
    "$FKST_MAINTENANCE_LOG" \
    || fail "newer generation retention was not reported"
)

failed_restart_retains_the_activation_generation() (
  load_implementation || exit 1
  local root obligation now
  root="$(mktemp -d -t hourly-maintenance-generation-retain.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  create_defer_policy_fixture "$root"
  obligation="$root/logs/restart-activation.state"
  export FKST_RESTART_ACTIVATION_STATE="$obligation"
  export FKST_RESTART_DEFER_STATE="$root/logs/restart-defer.state"
  now="$(date +%s)"
  write_activation_obligation_fixture "$obligation" "${now}-3-3" "$now"
  CHANGED=0
  restart_engine() { return 1; }

  restart_if_needed && fail "failed restart was accepted as activation reconciliation"
  command grep -q "generation=${now}-3-3" "$obligation" \
    || fail "restart failure erased the pending activation generation"
  command grep -q 'RESTART-OBLIGATION RETAINED.*restart failed' \
    "$FKST_MAINTENANCE_LOG" \
    || fail "restart-failure retention was not reported"
)

unusable_defer_timestamp_forces_restart() (
  local unusable="$1"
  load_implementation || exit 1
  local root obligation state now
  root="$(mktemp -d -t hourly-maintenance-invalid-defer-time.XXXXXX)" || exit 1
  trap "rm -rf '$root'" EXIT
  create_defer_policy_fixture "$root"
  grant_implement_lease "$root" "$$"
  state="$root/logs/restart-defer.state"
  obligation="$root/logs/restart-activation.state"
  export FKST_RESTART_ACTIVATION_STATE="$obligation"
  export FKST_RESTART_DEFER_STATE="$state"
  now="$(date +%s)"
  write_activation_obligation_fixture "$obligation" "${now}-4-4" "$now"
  printf '%s\n' "$unusable" > "$state"
  restart_engine() { : > "$root/restart-forced"; return 0; }

  restart_if_needed || fail "unusable defer timestamp should fail closed to restart"
  [[ -e "$root/restart-forced" ]] \
    || fail "unusable defer timestamp $unusable did not force a restart"
  command grep -q \
    "RESTART-DEFER INVALID.*started=$unusable.*forcing restart" \
    "$FKST_MAINTENANCE_LOG" \
    || fail "unusable defer timestamp $unusable was not reported"
)

leading_zero_defer_timestamp_forces_restart() {
  unusable_defer_timestamp_forces_restart 08
}

overflowing_defer_timestamp_forces_restart() {
  unusable_defer_timestamp_forces_restart 9223372036854775808
}

zombie_label_without_live_lease_restarts() (
  load_implementation || exit 1
  local root
  root="$(mktemp -d -t hourly-maintenance-zombie-label.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  create_defer_policy_fixture "$root"
  grant_implement_lease "$root" 999999

  restart_if_needed
  [[ -e "$root/run.calls" ]] \
    || fail "a zombie implementing label deferred restart without any live lease"
  ! command grep -q 'DEFER-RESTART' "$FKST_MAINTENANCE_LOG" \
    || fail "restart was deferred although no engine-owned lease was live"
  [[ ! -e "$GH_CALLS_FILE" ]] \
    || fail "repository labels participated in the restart gate"
)

live_lease_defers_restart_within_bound() (
  load_implementation || exit 1
  local root state
  root="$(mktemp -d -t hourly-maintenance-lease-defer.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  create_defer_policy_fixture "$root"
  grant_implement_lease "$root" "$$"
  export FKST_RESTART_DEFER_MAX_SECONDS=3600

  restart_if_needed || fail "restart deferral should exit successfully"
  [[ ! -e "$root/run.calls" ]] || fail "engine control ran during DEFER-RESTART"
  command grep -q 'DEFER-RESTART: 1 live implement lease' "$FKST_MAINTENANCE_LOG" \
    || fail "deferral did not report the engine-owned lease evidence"
  state="$root/logs/restart-defer.state"
  [[ -s "$state" ]] || fail "deferral did not record its bound-tracking start time"
  [[ ! -e "$GH_CALLS_FILE" ]] \
    || fail "repository labels participated in the restart gate"
)

defer_bound_exceeded_forces_restart() (
  load_implementation || exit 1
  local root state
  root="$(mktemp -d -t hourly-maintenance-lease-bound.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  create_defer_policy_fixture "$root"
  grant_implement_lease "$root" "$$"
  export FKST_RESTART_DEFER_MAX_SECONDS=600
  state="$root/logs/restart-defer.state"
  printf '%s\n' "$(( $(date +%s) - 4000 ))" > "$state"

  restart_if_needed
  [[ -e "$root/run.calls" ]] \
    || fail "an unbounded deferral survived past the configured bound"
  command grep -q 'FORCE-RESTART: defer bound exceeded' "$FKST_MAINTENANCE_LOG" \
    || fail "bound-exceeded forced restart was not recorded"
  [[ -e "$state" ]] || fail "failed forced restart erased the deferral window"
)
