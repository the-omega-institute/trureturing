#!/usr/bin/env bash
set -u
set -o pipefail
export LC_ALL=C
export LANG=C

REPOSITORY_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd -P)"
SCRIPT_UNDER_TEST="$REPOSITORY_ROOT/.fkst/scripts/hourly-maintenance.sh"
HOST_CONTRACT_LOADER="$REPOSITORY_ROOT/.fkst/scripts/host-contract.sh"
LAUNCHER_RENDERER="$REPOSITORY_ROOT/.fkst/scripts/render-maintenance-launcher.sh"
LAUNCHER_CONFORMANCE="$REPOSITORY_ROOT/.fkst/scripts/check-maintenance-launcher.sh"
CHECKOUT_CASES="$REPOSITORY_ROOT/.fkst/tests/hourly-maintenance-checkout-cases.sh"
RESTART_CASES="$REPOSITORY_ROOT/.fkst/tests/hourly-maintenance-restart-cases.sh"
COMPOSITION_CASES="$REPOSITORY_ROOT/.fkst/tests/hourly-maintenance-composition-cases.sh"
PASS_COUNT=0
FAIL_COUNT=0

fail() {
  echo "FAIL: $*" >&2
  exit 1
}

load_implementation() {
  [[ -f "$SCRIPT_UNDER_TEST" ]] \
    || fail "canonical implementation is missing: .fkst/scripts/hourly-maintenance.sh"
  # shellcheck disable=SC1090
  source "$SCRIPT_UNDER_TEST"
}

git_quiet() {
  command git "$@" >/dev/null 2>&1
}

configure_repository() {
  local repository="$1"
  command git -C "$repository" config user.name "Hourly Maintenance Fixture"
  command git -C "$repository" config user.email "hourly-maintenance@example.invalid"
}

create_platform_fixture() {
  local root="$1"
  PLATFORM_REMOTE="$root/platform-remote.git"
  PLATFORM_ROOT="$root/platform"
  git_quiet init --bare --initial-branch=dev "$PLATFORM_REMOTE" || return 1
  git_quiet clone "$PLATFORM_REMOTE" "$PLATFORM_ROOT" || return 1
  configure_repository "$PLATFORM_ROOT" || return 1
  printf 'old\n' > "$PLATFORM_ROOT/version"
  command git -C "$PLATFORM_ROOT" add version
  git_quiet -C "$PLATFORM_ROOT" commit -m old || return 1
  git_quiet -C "$PLATFORM_ROOT" push -u origin dev || return 1
  OLD_PLATFORM_REV="$(command git -C "$PLATFORM_ROOT" rev-parse HEAD)"
  printf 'new\n' > "$PLATFORM_ROOT/version"
  command git -C "$PLATFORM_ROOT" add version
  git_quiet -C "$PLATFORM_ROOT" commit -m new || return 1
  git_quiet -C "$PLATFORM_ROOT" push origin dev || return 1
  NEW_PLATFORM_REV="$(command git -C "$PLATFORM_ROOT" rev-parse HEAD)"
}

create_checkout_files() {
  local root="$1"
  CHECKOUT_ROOT="$root/checkout"
  mkdir -p "$CHECKOUT_ROOT/.fkst" "$root/logs" "$root/bin"
  printf '[external_sources.platform]\nrev = "%s"\n' "$OLD_PLATFORM_REV" \
    > "$CHECKOUT_ROOT/fkst.workspace.toml"
  printf 'deployed-lock-before\nwithout-final-newline' > "$CHECKOUT_ROOT/fkst.lock"
  printf '[external_sources.platform]\nrev = "%s"\n' "$OLD_PLATFORM_REV" \
    > "$CHECKOUT_ROOT/.fkst/fkst.workspace.toml"
  LOG_FILE="$root/logs/hourly-maintenance.log"
  FRAMEWORK_BIN="$root/bin/fkst-framework"
  TIMEOUT_BIN="$root/bin/timeout"
  cat > "$TIMEOUT_BIN" <<'SH'
#!/usr/bin/env bash
shift
exec "$@"
SH
  chmod +x "$TIMEOUT_BIN"
}

write_framework_stub() {
  local behavior="$1"
  cat > "$FRAMEWORK_BIN" <<SH
#!/usr/bin/env bash
printf 'host-lock-called\n' >> "${FRAMEWORK_CALLS_FILE}"
call_count="\$(wc -l < "${FRAMEWORK_CALLS_FILE}" | tr -d '[:space:]')"
printf 'lock-mutated-by-host-lock-%s\n' "\$call_count" > "${CHECKOUT_ROOT}/fkst.lock"
[[ "$behavior" == success || ( "$behavior" == fail-once && "\$call_count" -gt 1 ) ]]
SH
  chmod +x "$FRAMEWORK_BIN"
}

export_platform_environment() {
  export FKST_RUNTIME_ROOT="$(dirname -- "$CHECKOUT_ROOT")/runtime"
  mkdir -p "$FKST_RUNTIME_ROOT"
  export FKST_HOST_ROOT="$CHECKOUT_ROOT"
  export FKST_PLATFORM_ROOT="$PLATFORM_ROOT"
  export BIN="$FRAMEWORK_BIN"
  export FKST_MAINTENANCE_LOG="$LOG_FILE"
  export FKST_TIMEOUT_BIN="$TIMEOUT_BIN"
}

create_checkout_history_fixture() {
  local root="$1"
  CHECKOUT_REMOTE="$root/checkout-remote.git"
  CHECKOUT_ROOT="$root/checkout"
  CHECKOUT_WRITER="$root/checkout-writer"
  export FKST_RUNTIME_ROOT="$root/runtime"
  mkdir -p "$FKST_RUNTIME_ROOT"
  git_quiet init --bare --initial-branch=dev "$CHECKOUT_REMOTE" || return 1
  git_quiet clone "$CHECKOUT_REMOTE" "$CHECKOUT_ROOT" || return 1
  configure_repository "$CHECKOUT_ROOT" || return 1
  printf 'base\n' > "$CHECKOUT_ROOT/tracked"
  command git -C "$CHECKOUT_ROOT" add tracked
  git_quiet -C "$CHECKOUT_ROOT" commit -m base || return 1
  git_quiet -C "$CHECKOUT_ROOT" push -u origin dev || return 1
  CHECKOUT_BASE_REV="$(command git -C "$CHECKOUT_ROOT" rev-parse HEAD)"
  git_quiet clone "$CHECKOUT_REMOTE" "$CHECKOUT_WRITER" || return 1
  configure_repository "$CHECKOUT_WRITER" || return 1
}

advance_checkout_dev() {
  local contents="$1"
  printf '%s\n' "$contents" > "$CHECKOUT_WRITER/tracked"
  command git -C "$CHECKOUT_WRITER" add tracked
  git_quiet -C "$CHECKOUT_WRITER" commit -m "advance $contents" || return 1
  git_quiet -C "$CHECKOUT_WRITER" push origin dev || return 1
  CHECKOUT_DEV_REV="$(command git -C "$CHECKOUT_WRITER" rev-parse HEAD)"
}

deployed_top_level_workspace_is_authoritative() (
  load_implementation || exit 1
  local root
  root="$(mktemp -d -t hourly-maintenance-top-level.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  create_platform_fixture "$root" || exit 1
  create_checkout_files "$root" || exit 1
  FRAMEWORK_CALLS_FILE="$root/framework.calls"
  export FRAMEWORK_CALLS_FILE
  write_framework_stub success
  export_platform_environment
  local committed_before
  committed_before="$(command shasum -a 256 "$CHECKOUT_ROOT/.fkst/fkst.workspace.toml")"
  command find "$CHECKOUT_ROOT" -maxdepth 1 -type f -print \
    | command sed "s#^$CHECKOUT_ROOT/##" | command sort > "$root/paths.before"

  sync_platform || fail "platform sync should succeed"
  command grep -q "$NEW_PLATFORM_REV" "$CHECKOUT_ROOT/fkst.workspace.toml" \
    || fail "deployed top-level workspace pin was not updated"
  [[ "$committed_before" == "$(command shasum -a 256 "$CHECKOUT_ROOT/.fkst/fkst.workspace.toml")" ]] \
    || fail "committed .fkst workspace copy must not be touched (#2461)"
  command find "$CHECKOUT_ROOT" -maxdepth 1 -type f -print \
    | command sed "s#^$CHECKOUT_ROOT/##" | command sort > "$root/paths.after"
  command cmp -s "$root/paths.before" "$root/paths.after" \
    || fail "platform sync created a second restore representation"
)

activation_intent_is_write_ahead_at_cycle_entry() (
  load_implementation || exit 1
  local root output pending_state
  root="$(mktemp -d -t hourly-maintenance-write-ahead.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  create_composition_cycle_fixture "$root" '"alpha"' '"stale"' || exit 1
  mkdir -p "$root/runtime"
  export FKST_RUNTIME_ROOT="$root/runtime"
  pending_state="$FKST_RUNTIME_ROOT/hourly-maintenance.pending-activation"

  sed "s/$NEW_PLATFORM_REV/$OLD_PLATFORM_REV/" \
    "$CHECKOUT_ROOT/fkst.workspace.toml" > "$root/runtime-workspace.old-pin"
  mv "$root/runtime-workspace.old-pin" "$CHECKOUT_ROOT/fkst.workspace.toml"
  FRAMEWORK_BIN="$root/bin/fkst-framework"
  TIMEOUT_BIN="$root/bin/timeout"
  FRAMEWORK_CALLS_FILE="$root/framework.calls"
  export FRAMEWORK_CALLS_FILE BIN="$FRAMEWORK_BIN" FKST_TIMEOUT_BIN="$TIMEOUT_BIN"
  write_framework_stub success
  cat > "$TIMEOUT_BIN" <<'SH'
#!/usr/bin/env bash
shift
exec "$@"
SH
  chmod +x "$TIMEOUT_BIN"

  eval "$(declare -f write_platform_pin_revision \
    | sed '1s/write_platform_pin_revision/original_write_platform_pin_revision/')"
  write_platform_pin_revision() {
    [[ -f "$pending_state" ]] \
      || fail "platform pin mutation began before its activation intent was durable"
    command grep -q "^previous_platform_rev=$OLD_PLATFORM_REV$" "$pending_state" \
      || fail "write-ahead activation intent omitted the rollback origin"
    original_write_platform_pin_revision "$@"
  }
  sync_workspace_composition() {
    say "SYNTHETIC-COMPOSITION-FAIL after platform mutation"
    return 1
  }
  output="$root/output"

  main --host-config "$root/host.env" >"$output" 2>&1 \
    && fail "synthetic post-pin composition failure did not fail the cycle"
  command grep -q "$NEW_PLATFORM_REV" "$CHECKOUT_ROOT/fkst.workspace.toml" \
    || fail "fixture did not advance the platform pin before the later failure"
  [[ -f "$pending_state" ]] \
    || fail "later cycle failure lost the activation obligation"
  command grep -q 'SYNTHETIC-COMPOSITION-FAIL' "$output" \
    || fail "fixture did not reach the post-pin failure point: $(<"$output")"
)

host_lock_failure_reverts_to_previous_platform_revision() (
  load_implementation || exit 1
  local root
  root="$(mktemp -d -t hourly-maintenance-lock-rollback.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  create_platform_fixture "$root" || exit 1
  create_checkout_files "$root" || exit 1
  FRAMEWORK_CALLS_FILE="$root/framework.calls"
  export FRAMEWORK_CALLS_FILE
  write_framework_stub fail-once
  export_platform_environment

  sync_platform && fail "host-lock validation failure must fail the platform sync"
  command grep -q "$OLD_PLATFORM_REV" "$CHECKOUT_ROOT/fkst.workspace.toml" \
    || fail "failed upgrade did not restore the previous platform revision"
  ! command grep -q "$NEW_PLATFORM_REV" "$CHECKOUT_ROOT/fkst.workspace.toml" \
    || fail "failed upgrade left the new platform revision pinned"
  command grep -q 'lock-mutated-by-host-lock-2' "$CHECKOUT_ROOT/fkst.lock" \
    || fail "rollback did not regenerate the lock from the previous revision"
  [[ "$(wc -l < "$FRAMEWORK_CALLS_FILE" | tr -d '[:space:]')" == "2" ]] \
    || fail "rollback did not re-run the canonical lock writer"
)

post_restart_health_failure_reverts_to_previous_platform_revision() (
  load_implementation || exit 1
  local root
  root="$(mktemp -d -t hourly-maintenance-health-rollback.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  create_platform_fixture "$root" || exit 1
  create_checkout_files "$root" || exit 1
  FRAMEWORK_CALLS_FILE="$root/framework.calls"
  export FRAMEWORK_CALLS_FILE
  write_framework_stub success
  export_platform_environment
  export FKST_RUN_SCRIPT="$root/bin/run-engine"
  export FKST_LAUNCHD_LABEL="com.example.synthetic-fkst"
  cat > "$FKST_RUN_SCRIPT" <<SH
#!/usr/bin/env bash
printf '%s\n' "\$*" >> "$root/run.calls"
SH
  cat > "$root/bin/sleep" <<'SH'
#!/usr/bin/env bash
exit 0
SH
  cat > "$root/bin/launchctl" <<'SH'
#!/usr/bin/env bash
exit 0
SH
  cat > "$root/bin/pgrep" <<'SH'
#!/usr/bin/env bash
exit 1
SH
  chmod +x "$FKST_RUN_SCRIPT" "$root/bin/sleep" "$root/bin/launchctl" "$root/bin/pgrep"
  export PATH="$root/bin:$PATH"
  sync_platform || fail "platform sync setup should succeed"
  restart_engine && fail "failed health check must fail restart"
  command grep -q "$OLD_PLATFORM_REV" "$CHECKOUT_ROOT/fkst.workspace.toml" \
    || fail "health failure did not restore the previous platform revision"
  command grep -q 'lock-mutated-by-host-lock-2' "$CHECKOUT_ROOT/fkst.lock" \
    || fail "health rollback did not regenerate the lock from the previous revision"
)

worktree_gc_preserves_owned_or_dirty_lanes() (
  load_implementation || exit 1
  local root
  root="$(mktemp -d -t hourly-maintenance-worktree-gc.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  local remote="$root/remote.git"
  CHECKOUT_ROOT="$root/checkout"
  local lanes="$root/lanes"
  mkdir -p "$lanes" "$root/bin" "$root/logs"
  git_quiet init --bare --initial-branch=dev "$remote" || exit 1
  git_quiet clone "$remote" "$CHECKOUT_ROOT" || exit 1
  configure_repository "$CHECKOUT_ROOT" || exit 1
  printf 'base\n' > "$CHECKOUT_ROOT/tracked"
  command git -C "$CHECKOUT_ROOT" add tracked
  git_quiet -C "$CHECKOUT_ROOT" commit -m base || exit 1
  git_quiet -C "$CHECKOUT_ROOT" push -u origin dev || exit 1
  local owned="$lanes/lane-101-1"
  local dirty="$lanes/lane-102-1"
  local clean="$lanes/lane-103-1"
  git_quiet -C "$CHECKOUT_ROOT" worktree add -b lane-101 "$owned" origin/dev || exit 1
  git_quiet -C "$CHECKOUT_ROOT" worktree add -b lane-102 "$dirty" origin/dev || exit 1
  git_quiet -C "$CHECKOUT_ROOT" worktree add -b lane-103 "$clean" origin/dev || exit 1
  configure_repository "$owned" || exit 1
  printf 'owned\n' > "$owned/own-commit"
  command git -C "$owned" add own-commit
  git_quiet -C "$owned" commit -m owned || exit 1
  printf 'dirty\n' >> "$dirty/tracked"
  cat > "$root/bin/gh" <<'SH'
#!/usr/bin/env bash
[[ "$*" == *"issue view"* ]] || exit 8
printf 'CLOSED\n'
SH
  chmod +x "$root/bin/gh"
  export PATH="$root/bin:$PATH"
  export FKST_HOST_ROOT="$CHECKOUT_ROOT"
  export FKST_WORKTREE_ROOT="$lanes"
  export FKST_GITHUB_REPO="example/synthetic"
  export FKST_MAINTENANCE_LOG="$root/logs/hourly-maintenance.log"

  gc_worktrees || fail "worktree GC should be nonfatal"
  [[ -d "$owned" ]] || fail "lane with own commits was removed"
  [[ -d "$dirty" ]] || fail "lane with uncommitted work was removed"
  [[ ! -e "$clean" ]] || fail "clean closed-issue lane was not reclaimed"
)

gc_roots_are_canonical_and_never_the_filesystem_root() (
  load_implementation || exit 1
  local root
  root="$(mktemp -d -t hourly-maintenance-safe-root.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  type canonical_gc_root >/dev/null 2>&1 || fail "canonical GC-root validator is missing"
  [[ "$(canonical_gc_root "$root")" == "$(cd "$root" && pwd -P)" ]] \
    || fail "safe GC root was not canonicalized"
  ! canonical_gc_root "/tmp/.." >/dev/null 2>&1 \
    || fail "normalized filesystem root was accepted for GC"
)

stale_slot_gc_requires_a_genuinely_dead_owner() (
  load_implementation || exit 1
  local root
  root="$(mktemp -d -t hourly-maintenance-slot-gc.XXXXXX)" || exit 1
  mkdir -p "$root/slots/live.lock" "$root/slots/dead.lock" "$root/logs"
  sleep 30 &
  local live_pid=$!
  trap 'kill "$live_pid" 2>/dev/null || true; wait "$live_pid" 2>/dev/null || true; rm -rf "$root"' EXIT
  printf '%s\n' "$live_pid" > "$root/slots/live.lock/owner"
  local dead_pid=999999
  while command ps -p "$dead_pid" >/dev/null 2>&1; do dead_pid=$((dead_pid-1)); done
  printf '%s\n' "$dead_pid" > "$root/slots/dead.lock/owner"
  export FKST_REPORT_SLOT_ROOT="$root/slots"
  export FKST_MAINTENANCE_LOG="$root/logs/hourly-maintenance.log"

  reclaim_stale_slots || fail "slot GC should be nonfatal"
  [[ -d "$root/slots/live.lock" ]] || fail "live owner's slot was reclaimed"
  [[ ! -e "$root/slots/dead.lock" ]] || fail "dead owner's stale slot was retained"
)

slot_reclaim_rechecks_owner_after_atomic_claim() (
  load_implementation || exit 1
  local root
  root="$(mktemp -d -t hourly-maintenance-slot-race.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  mkdir -p "$root/slots/race.lock" "$root/logs"
  printf '7001\n' > "$root/slots/race.lock/owner"
  export FKST_REPORT_SLOT_ROOT="$root/slots"
  export FKST_MAINTENANCE_LOG="$root/logs/hourly-maintenance.log"
  local kill_checks=0
  kill() {
    [[ "$1" == "-0" ]] || return 1
    kill_checks=$((kill_checks + 1))
    [[ "$kill_checks" -ge 2 ]]
  }
  ps() { return 0; }

  reclaim_stale_slots || fail "racing slot reclaim should be nonfatal"
  [[ -d "$root/slots/race.lock" ]] || fail "slot was removed after its owner became live"
  [[ ! -e "$root/slots/race.lock.reclaim-guard" ]] \
    || fail "reclaim guard leaked after owner recheck"
)

revision_rollback_lock_failure_is_not_reported_as_reverted() (
  load_implementation || exit 1
  local root
  root="$(mktemp -d -t hourly-maintenance-rollback-honesty.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  create_platform_fixture "$root" || exit 1
  create_checkout_files "$root" || exit 1
  FRAMEWORK_CALLS_FILE="$root/framework.calls"
  export FRAMEWORK_CALLS_FILE
  write_framework_stub success
  export_platform_environment
  export FKST_RUN_SCRIPT="$root/bin/run-engine"
  export FKST_LAUNCHD_LABEL="com.example.synthetic-fkst"
  printf '#!/usr/bin/env bash\nexit 0\n' > "$FKST_RUN_SCRIPT"
  printf '#!/usr/bin/env bash\nexit 0\n' > "$root/bin/sleep"
  printf '#!/usr/bin/env bash\nexit 0\n' > "$root/bin/launchctl"
  printf '#!/usr/bin/env bash\nexit 1\n' > "$root/bin/pgrep"
  chmod +x "$FKST_RUN_SCRIPT" "$root/bin/sleep" "$root/bin/launchctl" "$root/bin/pgrep"
  export PATH="$root/bin:$PATH"

  sync_platform || fail "platform sync setup should succeed"
  write_framework_stub fail
  restart_engine && fail "health failure with failed revision rollback must fail"
  command grep -q "$OLD_PLATFORM_REV" "$CHECKOUT_ROOT/fkst.workspace.toml" \
    || fail "rollback did not derive the previous platform revision"
  command grep -q 'lock-mutated-by-host-lock-2' "$CHECKOUT_ROOT/fkst.lock" \
    || fail "rollback did not attempt lock regeneration from the previous revision"
  command grep -q 'ROLLBACK-HOST-LOCK-FAIL' "$FKST_MAINTENANCE_LOG" \
    || fail "revision-derived rollback failure was not reported"
  ! command grep -q 'reverted platform' "$FKST_MAINTENANCE_LOG" \
    || fail "failed rollback was falsely reported as reverted"
)

pin_write_failure_reverts_from_previous_revision() (
  load_implementation || exit 1
  local root
  root="$(mktemp -d -t hourly-maintenance-pin-write-rollback.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  create_platform_fixture "$root" || exit 1
  create_checkout_files "$root" || exit 1
  FRAMEWORK_CALLS_FILE="$root/framework.calls"
  export FRAMEWORK_CALLS_FILE
  write_framework_stub success
  export_platform_environment
  export MV_CALLS_FILE="$root/mv.calls"
  real_mv="$(command -v mv)"
  cat > "$root/bin/mv" <<'SH'
#!/usr/bin/env bash
if [[ "${!#}" != "$FKST_HOST_ROOT/fkst.workspace.toml" ]]; then
  exec "$REAL_MV" "$@"
fi
count=0
[[ ! -f "$MV_CALLS_FILE" ]] || count="$(<"$MV_CALLS_FILE")"
count=$((count + 1))
printf '%s\n' "$count" > "$MV_CALLS_FILE"
[[ "$count" -gt 1 ]] || exit 9
exec "$REAL_MV" "$@"
SH
  chmod +x "$root/bin/mv"
  export REAL_MV="$real_mv"
  export PATH="$root/bin:$PATH"

  sync_platform && fail "pin-write failure must fail platform sync"
  command grep -q "$OLD_PLATFORM_REV" "$CHECKOUT_ROOT/fkst.workspace.toml" \
    || fail "pin-write failure did not restore the previous revision"
  [[ "$(<"$MV_CALLS_FILE")" == "2" ]] \
    || fail "pin-write rollback did not re-run the canonical revision writer"
  command grep -q 'lock-mutated-by-host-lock-1' "$CHECKOUT_ROOT/fkst.lock" \
    || fail "pin-write rollback did not regenerate the lock"
  command grep -q 'PLATFORM-PIN-WRITE-FAIL; reverted to' "$FKST_MAINTENANCE_LOG" \
    || fail "successful revision-derived pin rollback was not reported"
)

write_host_contract_fixture() {
  local root="$1"
  local bot_login="$2"
  local integration_branch="$3"
  FIXTURE_HOST_ROOT="$root/host-checkout"
  FIXTURE_HOST_CONFIG="$root/host.env"
  FIXTURE_LAUNCHER_PATH="$root/launchd/maintenance.plist"
  mkdir -p \
    "$FIXTURE_HOST_ROOT/.fkst/scripts" \
    "$FIXTURE_HOST_ROOT/.fkst/workflows" \
    "$root/bin" \
    "$root/durable" \
    "$root/launchd" \
    "$root/logs" \
    "$root/platform" \
    "$root/rate-pools" \
    "$root/runtime/worktrees" \
    "$root/supervisor/slots"
  command cp "$REPOSITORY_ROOT/.fkst/deploy.env" "$FIXTURE_HOST_ROOT/.fkst/deploy.env"
  command cp "$REPOSITORY_ROOT/.fkst/fkst.workspace.toml" \
    "$FIXTURE_HOST_ROOT/.fkst/fkst.workspace.toml"
  command cp "$REPOSITORY_ROOT/.fkst/fkst.workspace.toml" \
    "$FIXTURE_HOST_ROOT/fkst.workspace.toml"
  printf '#!/usr/bin/env bash\nexit 0\n' > "$root/bin/fkst-framework"
  printf '#!/usr/bin/env bash\nshift\nexec "$@"\n' > "$root/bin/timeout"
  printf '#!/usr/bin/env bash\nexit 0\n' > "$FIXTURE_HOST_ROOT/.fkst/scripts/run.sh"
  chmod +x \
    "$root/bin/fkst-framework" \
    "$root/bin/timeout" \
    "$FIXTURE_HOST_ROOT/.fkst/scripts/run.sh"
  {
    printf 'BIN=%s\n' "$root/bin/fkst-framework"
    printf 'FKST_HOST_ROOT=%s\n' "$FIXTURE_HOST_ROOT"
    printf 'FKST_PLATFORM_ROOT=%s\n' "$root/platform"
    printf 'FKST_DURABLE_ROOT=%s\n' "$root/durable"
    printf 'FKST_RUNTIME_ROOT=%s\n' "$root/runtime"
    printf 'FKST_RATE_POOL_ROOT=%s\n' "$root/rate-pools"
    printf 'FKST_WORKFLOW_CATALOG_ROOT=%s\n' "$FIXTURE_HOST_ROOT/.fkst/workflows"
    printf 'PATH=%s\n' "$root/bin:/usr/bin:/bin"
    printf '%s\n' 'source "$FKST_HOST_ROOT/.fkst/deploy.env"'
    printf 'export FKST_GITHUB_BOT_LOGIN=%s\n' "$bot_login"
    printf 'export FKST_DEVLOOP_INTEGRATION_BRANCH=%s\n' "$integration_branch"
    printf 'export FKST_DEVLOOP_MANAGED_BOT_LOGINS=%s\n' "$bot_login"
    printf 'export FKST_RUN_SCRIPT=%s\n' "$FIXTURE_HOST_ROOT/.fkst/scripts/run.sh"
    printf 'export FKST_MAINTENANCE_LOG=%s\n' "$root/logs/hourly-maintenance.log"
    printf 'export FKST_MAINTENANCE_LAUNCHER_LOG=%s\n' "$root/logs/maintenance-launcher.log"
    printf 'export FKST_WORKTREE_ROOT=%s\n' "$root/runtime/worktrees"
    printf 'export FKST_REPORT_SLOT_ROOT=%s\n' "$root/supervisor/slots"
    printf 'export FKST_TIMEOUT_BIN=%s\n' "$root/bin/timeout"
    printf 'export FKST_LAUNCHD_LABEL=%s\n' 'local.fkst.synthetic.supervise'
    printf 'export FKST_MAINTENANCE_LAUNCHD_LABEL=%s\n' 'local.fkst.synthetic.maintenance'
    printf 'export FKST_MAINTENANCE_LAUNCHER_PATH=%s\n' "$FIXTURE_LAUNCHER_PATH"
    printf 'export FKST_BASH_BIN=%s\n' /bin/bash
    printf 'export FKST_ZSH_BIN=%s\n' /bin/zsh
    printf 'export FKST_PYTHON_BIN=%s\n' "$(command -v python3)"
    printf 'export FKST_SUPERVISE_LAUNCHER_LOG=%s\n' "$root/logs/supervise-launcher.log"
    printf 'export FKST_SUPERVISE_LAUNCHER_PATH=%s\n' "$root/launchd/supervise.plist"
  } > "$FIXTURE_HOST_CONFIG"
}
. "$REPOSITORY_ROOT/.fkst/tests/support/hourly-maintenance-launchd-cases.sh"

host_config_rejects_shell_control_flow_without_evaluation() (
  local root output pwned
  root="$(mktemp -d -t hourly-maintenance-host-data.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  write_host_contract_fixture "$root" second-host-bot integration-second-host
  output="$root/entrypoint.output"
  pwned="$root/evaluated-shell"
  printf 'FKST_HOST_ROOT=$(touch %s)\n' "$pwned" >> "$FIXTURE_HOST_CONFIG"

  if env -i HOME="$root/home" PATH="/usr/bin:/bin" \
      /bin/bash "$SCRIPT_UNDER_TEST" --validate-only --host-config "$FIXTURE_HOST_CONFIG" \
      >"$output" 2>&1; then
    fail "host config containing shell control flow was accepted"
  fi
  [[ ! -e "$pwned" ]] || fail "host config was evaluated as shell"
  command grep -q 'invalid data line' "$output" \
    || fail "strict parser did not identify the rejected data line: $(<"$output")"
)

fictional_second_host_launcher_is_portable() (
  local root rendered
  root="$(mktemp -d -t maintenance-launcher-render.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  write_host_contract_fixture "$root" second-host-bot integration-second-host
  rendered="$root/rendered.plist"

  HOST_CONFIG="$FIXTURE_HOST_CONFIG" OUTPUT="$rendered" \
    /bin/bash "$LAUNCHER_RENDERER" \
    || fail "fictional second-host launcher did not render"
  command grep -qF "<string>$FIXTURE_HOST_ROOT</string>" "$rendered" \
    || fail "rendered launcher did not contain the fictional checkout"
  command grep -qF '<string>second-host-bot</string>' "$rendered" \
    || fail "rendered launcher did not contain the fictional bot login"
  command grep -qF '<string>integration-second-host</string>' "$rendered" \
    || fail "rendered launcher did not contain the fictional integration branch"
  command grep -qF "<string>$root/logs/maintenance-launcher.log</string>" "$rendered" \
    || fail "rendered launcher did not use the distinct launcher log"
  command grep -qF '<string>hourly-maintenance</string>' "$rendered" \
    || fail "rendered launcher does not invoke the Make entrypoint"
  ! command grep -qF 'safe-platform-sync.sh' "$rendered" \
    || fail "rendered launcher still invokes a host-local script copy"
)

launcher_conformance_compares_rendered_and_deployed_bytes() (
  local root deployed
  root="$(mktemp -d -t maintenance-launcher-conformance.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  write_host_contract_fixture "$root" second-host-bot integration-second-host
  deployed="$root/deployed.plist"
  HOST_CONFIG="$FIXTURE_HOST_CONFIG" OUTPUT="$deployed" \
    /bin/bash "$LAUNCHER_RENDERER" || exit 1

  HOST_CONFIG="$FIXTURE_HOST_CONFIG" DEPLOYED_LAUNCHER="$deployed" \
    /bin/bash "$LAUNCHER_CONFORMANCE" \
    || fail "byte-identical deployed launcher was rejected"
  printf '\n<!-- drift -->\n' >> "$deployed"
  if HOST_CONFIG="$FIXTURE_HOST_CONFIG" DEPLOYED_LAUNCHER="$deployed" \
      /bin/bash "$LAUNCHER_CONFORMANCE" >/dev/null 2>&1; then
    fail "drifted deployed launcher was accepted"
  fi
)

run_test() {
  local name="$1"
  shift
  if "$@"; then
    PASS_COUNT=$((PASS_COUNT + 1))
    printf 'ok %d - %s\n' "$((PASS_COUNT + FAIL_COUNT))" "$name"
  else
    FAIL_COUNT=$((FAIL_COUNT + 1))
    printf 'not ok %d - %s\n' "$((PASS_COUNT + FAIL_COUNT))" "$name"
  fi
}

[[ -f "$RESTART_CASES" ]] || fail "restart behavior cases are missing"
# shellcheck disable=SC1090
source "$RESTART_CASES"
[[ -f "$COMPOSITION_CASES" ]] || fail "composition behavior cases are missing"
# shellcheck disable=SC1090
source "$COMPOSITION_CASES"
[[ -f "$CHECKOUT_CASES" ]] || fail "checkout behavior cases are missing"
# shellcheck disable=SC1090
source "$CHECKOUT_CASES"

run_test "deployed top-level workspace is authoritative" deployed_top_level_workspace_is_authoritative
run_test "activation intent is write-ahead at the cycle entry point" activation_intent_is_write_ahead_at_cycle_entry
run_test "host-lock failure reverts to previous platform revision" host_lock_failure_reverts_to_previous_platform_revision
run_test "post-restart health failure reverts to previous platform revision" post_restart_health_failure_reverts_to_previous_platform_revision
run_test "checkout fast-forwards only clean ancestors" checkout_fast_forwards_only_clean_ancestors
run_test "checkout untracked files do not block fast-forward" checkout_untracked_files_do_not_block_fast_forward
run_test "checkout divergence refuses auto fast-forward" checkout_divergence_refuses_auto_fast_forward
run_test "checkout status failure refuses auto fast-forward" checkout_status_failure_refuses_auto_fast_forward
run_test "tracked package removal propagates after checkout fast-forward" tracked_package_removal_propagates_after_checkout_fast_forward
run_test "tracked package addition propagates after checkout fast-forward" tracked_package_addition_propagates_after_checkout_fast_forward
run_test "platform-current cycle still propagates composition" platform_current_cycle_still_propagates_composition
run_test "post-write composition drift fails closed with differences" post_write_composition_drift_fails_closed_with_differences
run_test "composition-only propagation does not trigger restart" composition_only_propagation_does_not_trigger_restart
run_test "local implement work controls pending restart" local_implement_work_controls_pending_restart
run_test "deferred activation retains platform rollback origin" deferred_activation_retains_platform_rollback_origin
run_test "verified restart cannot clear newer activation generation" verified_restart_cannot_clear_newer_activation_generation
run_test "octal defer timestamp forces restart" octal_defer_timestamp_forces_restart
run_test "overflowing defer timestamp forces restart" overflowing_defer_timestamp_forces_restart
run_test "failed restart retains pending activation" failed_restart_retains_pending_activation
run_test "orphaned defer state is not dropped" orphaned_defer_state_is_not_dropped
run_test "worktree GC preserves owned or dirty lanes" worktree_gc_preserves_owned_or_dirty_lanes
run_test "GC roots are canonical and never filesystem root" gc_roots_are_canonical_and_never_the_filesystem_root
run_test "stale slot GC requires a genuinely dead owner" stale_slot_gc_requires_a_genuinely_dead_owner
run_test "slot reclaim rechecks owner after atomic claim" slot_reclaim_rechecks_owner_after_atomic_claim
run_test "late engine PID is accepted before restart budget expires" late_engine_pid_is_accepted_before_restart_budget_expires
run_test "restart timeout with launchd in service does not roll back platform" restart_timeout_with_launchd_in_service_does_not_roll_back_platform
run_test "restart timeout with launchd absent rolls back platform" restart_timeout_with_launchd_absent_rolls_back_platform
run_test "unchanged PID remains unhealthy after restart budget" unchanged_pid_remains_unhealthy_after_restart_budget
run_test "restart requires successful stop" restart_requires_successful_stop
run_test "revision rollback lock failure is not reported as reverted" revision_rollback_lock_failure_is_not_reported_as_reverted
run_test "pin-write failure reverts from previous revision" pin_write_failure_reverts_from_previous_revision
run_test "maintenance delegates launchd conformance gate" maintenance_delegates_launchd_conformance_gate
run_test "launchd conformance failure fails maintenance cycle" launchd_conformance_failure_fails_maintenance_cycle
run_test "missing launchd provider key fails maintenance cycle" missing_launchd_provider_key_fails_maintenance_cycle
run_test "tracked entrypoint loads strict host config" tracked_entrypoint_loads_strict_host_config
run_test "VALIDATE_ONLY rejects a missing supervise provider key" validate_only_rejects_missing_supervise_provider_key
run_test "bring-up bootstraps supervise before inventory check" bring_up_document_bootstraps_supervise_before_inventory_check
run_test "stale deployed repository contract does not block checkout refresh" stale_deployed_repository_contract_does_not_block_checkout_refresh
run_test "host config rejects shell control flow without evaluation" host_config_rejects_shell_control_flow_without_evaluation
run_test "fictional second-host launcher is portable" fictional_second_host_launcher_is_portable
run_test "launcher conformance compares rendered and deployed bytes" launcher_conformance_compares_rendered_and_deployed_bytes

printf 'behavior tests: %d passed, %d failed, %d total\n' \
  "$PASS_COUNT" "$FAIL_COUNT" "$((PASS_COUNT + FAIL_COUNT))"
[[ "$FAIL_COUNT" -eq 0 ]]
