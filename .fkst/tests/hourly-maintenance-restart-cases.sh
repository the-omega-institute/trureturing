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
  PLATFORM_CHANGED=1
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
  command cp "$CHECKOUT_ROOT/fkst.workspace.toml" "$root/workspace.before"
  command cp "$CHECKOUT_ROOT/fkst.lock" "$root/lock.before"

  sync_platform || fail "platform sync setup should succeed"
  restart_engine && fail "missing launchd service and PID must be unhealthy"
  command cmp -s "$root/workspace.before" "$CHECKOUT_ROOT/fkst.workspace.toml" \
    || fail "confirmed startup failure did not restore workspace bytes"
  command cmp -s "$root/lock.before" "$CHECKOUT_ROOT/fkst.lock" \
    || fail "confirmed startup failure did not restore lock bytes"
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
  PLATFORM_CHANGED=0

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
  [[ ! -e "$state" ]] || fail "forced restart did not clear the deferral window"
)

