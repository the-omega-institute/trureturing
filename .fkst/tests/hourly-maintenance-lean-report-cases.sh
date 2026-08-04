# Lean-report rebuild cases sourced by hourly-maintenance-behavior.sh.

checkout_lean_change_rebuilds_report_before_restart() (
  load_implementation || exit 1
  local root obligation make_calls
  root="$(mktemp -d -t hourly-maintenance-lean-report.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  mkdir -p "$root/bin" "$root/logs" "$root/slots"
  LOG_FILE="$root/logs/hourly-maintenance.log"
  export FKST_MAINTENANCE_LOG="$LOG_FILE"
  export FKST_RESTART_ACTIVATION_STATE="$root/logs/restart-activation.state"
  export FKST_RESTART_DEFER_STATE="$root/logs/restart-defer.state"
  export FKST_REPORT_SLOT_ROOT="$root/slots"
  create_checkout_history_fixture "$root" || exit 1
  printf 'def answer : Nat := 42\n' > "$CHECKOUT_WRITER/Answer.lean"
  command git -C "$CHECKOUT_WRITER" add Answer.lean
  git_quiet -C "$CHECKOUT_WRITER" commit -m "advance Lean source" || exit 1
  git_quiet -C "$CHECKOUT_WRITER" push origin dev || exit 1
  CHECKOUT_DEV_REV="$(command git -C "$CHECKOUT_WRITER" rev-parse HEAD)"
  export FKST_HOST_ROOT="$CHECKOUT_ROOT"
  obligation="$FKST_RESTART_ACTIVATION_STATE"
  make_calls="$root/make.calls"
  export MAKE_CALLS="$make_calls"
  cat > "$root/bin/make" <<'SH'
#!/usr/bin/env bash
printf '%s\n' "$*" >> "$MAKE_CALLS"
SH
  chmod +x "$root/bin/make"
  export FKST_MAKE_BIN="$root/bin/make"
  cat > "$root/bin/timeout" <<'SH'
#!/usr/bin/env bash
shift
exec "$@"
SH
  cat > "$root/bin/dotnet" <<'SH'
#!/usr/bin/env bash
printf 'LEAN_REPORT_STATUS valid\n'
SH
  chmod +x "$root/bin/timeout" "$root/bin/dotnet"
  export FKST_TIMEOUT_BIN="$root/bin/timeout"
  export FKST_DOTNET_BIN="$root/bin/dotnet"

  sync_checkout || fail "Lean-changing checkout sync should succeed"
  command grep -q '^lean_report_required=1$' "$obligation" \
    || fail "Lean-changing fast-forward did not persist its report obligation before mutation"
  restart_engine() {
    [[ -s "$make_calls" ]] || fail "restart began before the Lean report was rebuilt"
  }
  engine_pid() { return 0; }

  restart_if_needed || fail "successful Lean report rebuild should reconcile activation"
  [[ "$(<"$make_calls")" == "-C $CHECKOUT_ROOT lean-report" ]] \
    || fail "maintenance did not delegate rebuild to make lean-report: $(<"$make_calls")"
  [[ ! -e "$obligation" ]] \
    || fail "successful rebuild and restart did not clear the activation obligation"
  command grep -q 'LEAN-REPORT-REBUILD OK' "$LOG_FILE" \
    || fail "successful report obligation discharge was not reported"
)

checkout_non_lean_change_does_not_rebuild_report() (
  load_implementation || exit 1
  local root obligation make_calls
  root="$(mktemp -d -t hourly-maintenance-no-lean-report.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  mkdir -p "$root/bin" "$root/logs" "$root/slots"
  LOG_FILE="$root/logs/hourly-maintenance.log"
  export FKST_MAINTENANCE_LOG="$LOG_FILE"
  export FKST_RESTART_ACTIVATION_STATE="$root/logs/restart-activation.state"
  export FKST_RESTART_DEFER_STATE="$root/logs/restart-defer.state"
  export FKST_REPORT_SLOT_ROOT="$root/slots"
  create_checkout_history_fixture "$root" || exit 1
  advance_checkout_dev documentation-only || exit 1
  export FKST_HOST_ROOT="$CHECKOUT_ROOT"
  obligation="$FKST_RESTART_ACTIVATION_STATE"
  make_calls="$root/make.calls"
  export MAKE_CALLS="$make_calls"
  cat > "$root/bin/make" <<'SH'
#!/usr/bin/env bash
printf '%s\n' "$*" >> "$MAKE_CALLS"
SH
  chmod +x "$root/bin/make"
  export FKST_MAKE_BIN="$root/bin/make"

  sync_checkout || fail "non-Lean checkout sync should succeed"
  command grep -q '^lean_report_required=0$' "$obligation" \
    || fail "non-Lean fast-forward did not persist the absence of a report obligation"
  restart_engine() { return 0; }
  engine_pid() { return 0; }

  restart_if_needed || fail "non-Lean activation should reconcile"
  [[ ! -e "$make_calls" ]] \
    || fail "non-Lean fast-forward invoked an unnecessary report rebuild: $(<"$make_calls")"
)

failed_lean_report_rebuild_fails_cycle_and_retains_obligation() (
  load_implementation || exit 1
  local root obligation
  root="$(mktemp -d -t hourly-maintenance-lean-report-fail.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  mkdir -p "$root/bin" "$root/logs" "$root/slots"
  LOG_FILE="$root/logs/hourly-maintenance.log"
  export FKST_MAINTENANCE_LOG="$LOG_FILE"
  export FKST_RESTART_ACTIVATION_STATE="$root/logs/restart-activation.state"
  export FKST_RESTART_DEFER_STATE="$root/logs/restart-defer.state"
  export FKST_REPORT_SLOT_ROOT="$root/slots"
  create_checkout_history_fixture "$root" || exit 1
  printf 'def brokenWindow : Nat := 7\n' > "$CHECKOUT_WRITER/BrokenWindow.lean"
  command git -C "$CHECKOUT_WRITER" add BrokenWindow.lean
  git_quiet -C "$CHECKOUT_WRITER" commit -m "advance second Lean source" || exit 1
  git_quiet -C "$CHECKOUT_WRITER" push origin dev || exit 1
  CHECKOUT_DEV_REV="$(command git -C "$CHECKOUT_WRITER" rev-parse HEAD)"
  export FKST_HOST_ROOT="$CHECKOUT_ROOT"
  obligation="$FKST_RESTART_ACTIVATION_STATE"
  cat > "$root/bin/make" <<'SH'
#!/usr/bin/env bash
printf 'synthetic lean-report failure\n' >&2
exit 9
SH
  chmod +x "$root/bin/make"
  export FKST_MAKE_BIN="$root/bin/make"

  sync_checkout || fail "Lean-changing checkout sync should reach its pending rebuild"
  restart_engine() { : > "$root/restart-called"; return 0; }
  engine_pid() { return 0; }
  host_contract_load() { return 0; }
  validate_configuration() { return 0; }
  host_contract_require() { return 0; }
  sync_platform() { return 0; }
  sync_checkout() { return 0; }
  sync_workspace_composition() { return 0; }
  gc_worktrees() { return 0; }
  gc_stuck_lean_builds() { return 0; }
  check_launchd_conformance() { return 0; }

  main --host-config "$root/host.env" \
    && fail "failed Lean report rebuild was reported as a successful cycle"
  command grep -q '^lean_report_required=1$' "$obligation" \
    || fail "failed rebuild erased its durable report obligation"
  [[ ! -e "$root/restart-called" ]] \
    || fail "engine restarted even though its Lean report rebuild failed"
  command grep -q 'LEAN-REPORT-REBUILD FAIL' "$LOG_FILE" \
    || fail "failed report rebuild was not reported loudly"
)

blocked_lean_fast_forward_does_not_rebuild_report() (
  load_implementation || exit 1
  local root make_calls checkout_before
  root="$(mktemp -d -t hourly-maintenance-blocked-lean-report.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  mkdir -p "$root/bin" "$root/logs" "$root/slots"
  LOG_FILE="$root/logs/hourly-maintenance.log"
  export FKST_MAINTENANCE_LOG="$LOG_FILE"
  export FKST_RESTART_ACTIVATION_STATE="$root/logs/restart-activation.state"
  export FKST_RESTART_DEFER_STATE="$root/logs/restart-defer.state"
  export FKST_REPORT_SLOT_ROOT="$root/slots"
  create_checkout_history_fixture "$root" || exit 1
  printf 'def remoteVersion : Nat := 1\n' > "$CHECKOUT_WRITER/Conflict.lean"
  command git -C "$CHECKOUT_WRITER" add Conflict.lean
  git_quiet -C "$CHECKOUT_WRITER" commit -m "add conflicting Lean source" || exit 1
  git_quiet -C "$CHECKOUT_WRITER" push origin dev || exit 1
  CHECKOUT_DEV_REV="$(command git -C "$CHECKOUT_WRITER" rev-parse HEAD)"
  printf 'def hostOwnedVersion : Nat := 2\n' > "$CHECKOUT_ROOT/Conflict.lean"
  checkout_before="$(command git -C "$CHECKOUT_ROOT" rev-parse HEAD)"
  export FKST_HOST_ROOT="$CHECKOUT_ROOT"
  make_calls="$root/make.calls"
  export MAKE_CALLS="$make_calls"
  cat > "$root/bin/make" <<'SH'
#!/usr/bin/env bash
printf '%s\n' "$*" >> "$MAKE_CALLS"
SH
  chmod +x "$root/bin/make"
  export FKST_MAKE_BIN="$root/bin/make"

  sync_checkout || fail "blocked Lean fast-forward should remain a handled checkout refusal"
  [[ "$(command git -C "$CHECKOUT_ROOT" rev-parse HEAD)" == "$checkout_before" ]] \
    || fail "conflicting untracked Lean file did not block the fast-forward"
  restart_engine() { return 0; }
  engine_pid() { return 0; }

  restart_if_needed || fail "blocked checkout intent should reconcile without a report rebuild"
  [[ ! -e "$make_calls" ]] \
    || fail "blocked Lean fast-forward rebuilt a report for sources that were never deployed: $(<"$make_calls")"
  command grep -q 'LEAN-REPORT-REBUILD NOT REQUIRED.*target not deployed' "$LOG_FILE" \
    || fail "skipped rebuild did not report why the write-ahead intent no longer applied"
)

configure_lean_report_reconciliation_fixture() {
  local root="$1"
  export LEAN_REPORT_STATE="$root/lean-report.state"
  export LEAN_REPORT_DOTNET_CALLS="$root/dotnet.calls"
  export LEAN_REPORT_MAKE_CALLS="$root/make.calls"
  export FKST_DOTNET_BIN="$root/bin/dotnet"
  export FKST_MAKE_BIN="$root/bin/make"
  export FKST_TIMEOUT_BIN="$root/bin/timeout"
  printf 'invalid\n' > "$LEAN_REPORT_STATE"
  cat > "$FKST_TIMEOUT_BIN" <<'SH'
#!/usr/bin/env bash
if [[ "${LEAN_REPORT_PROBE_MODE:-state}" == "timeout" ]]; then
  exit 124
fi
shift
exec "$@"
SH
  cat > "$FKST_DOTNET_BIN" <<'SH'
#!/usr/bin/env bash
printf '%s\n' "$*" >> "$LEAN_REPORT_DOTNET_CALLS"
if [[ "${LEAN_REPORT_PROBE_MODE:-state}" == "digest-failure" ]]; then
  printf 'DIGEST_STATUS_INVALID CAS blob is missing\n' >&2
  exit 2
fi
if [[ "$(<"$LEAN_REPORT_STATE")" == "valid" ]]; then
  printf 'LEAN_REPORT_STATUS valid\n'
  exit 0
fi
printf 'LEAN_REPORT_STATUS invalid Raw Lean report is missing modules: D5/S1/Stale.lean\n'
exit 1
SH
  cat > "$FKST_MAKE_BIN" <<'SH'
#!/usr/bin/env bash
printf '%s\n' "$*" >> "$LEAN_REPORT_MAKE_CALLS"
[[ "$*" == "-C $FKST_HOST_ROOT lean-report" ]] || exit 8
if [[ "${LEAN_REPORT_REBUILD_LEAVES_INVALID:-0}" != "1" ]]; then
  printf 'valid\n' > "$LEAN_REPORT_STATE"
fi
SH
  chmod +x "$FKST_TIMEOUT_BIN" "$FKST_DOTNET_BIN" "$FKST_MAKE_BIN"
}

stub_report_cycle_dependencies() {
  host_contract_load() { HOST_CONFIG="$1"; export HOST_CONFIG; }
  validate_configuration() { return 0; }
  host_contract_require() { return 0; }
  sync_platform() { return 0; }
  sync_workspace_composition() { return 0; }
  gc_worktrees() { return 0; }
  gc_stuck_lean_builds() { return 0; }
  restart_engine() { return 0; }
  engine_pid() { return 1; }
  check_launchd_conformance() { return 0; }
}

already_current_stale_checkout_rebuilds_and_revalidates_report() (
  load_implementation || exit 1
  local root checkout_head
  root="$(mktemp -d -t hourly-maintenance-stale-report.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  mkdir -p "$root/bin" "$root/logs" "$root/slots"
  LOG_FILE="$root/logs/hourly-maintenance.log"
  export FKST_MAINTENANCE_LOG="$LOG_FILE"
  export FKST_RESTART_ACTIVATION_STATE="$root/logs/restart-activation.state"
  export FKST_RESTART_DEFER_STATE="$root/logs/restart-defer.state"
  export FKST_REPORT_SLOT_ROOT="$root/slots"
  create_checkout_history_fixture "$root" || exit 1
  export FKST_HOST_ROOT="$CHECKOUT_ROOT"
  checkout_head="$(command git -C "$CHECKOUT_ROOT" rev-parse HEAD)"
  configure_lean_report_reconciliation_fixture "$root"
  stub_report_cycle_dependencies

  main --host-config "$root/host.env" \
    || fail "an already-current stale report should be repaired"

  [[ "$(<"$LEAN_REPORT_STATE")" == "valid" ]] \
    || fail "maintenance left the already-current checkout with an invalid report"
  [[ "$(command git -C "$CHECKOUT_ROOT" rev-parse HEAD)" == "$checkout_head" ]] \
    || fail "the stale-report regression unexpectedly changed checkout HEAD"
  [[ "$(wc -l < "$LEAN_REPORT_MAKE_CALLS" | tr -d '[:space:]')" == "1" ]] \
    || fail "stale report was not rebuilt exactly once"
  [[ "$(wc -l < "$LEAN_REPORT_DOTNET_CALLS" | tr -d '[:space:]')" == "2" ]] \
    || fail "report repair did not perform one observation and one post-repair observation"
  command grep -q 'lean-report-status' "$LEAN_REPORT_DOTNET_CALLS" \
    || fail "maintenance did not use the typed raw-report status command"
  command grep -q 'LEAN-REPORT-RECONCILE OK' "$LOG_FILE" \
    || fail "successful desired-state reconciliation was not reported"

  main --host-config "$root/host.env" \
    || fail "the next current cycle should observe the repaired report"
  [[ "$(wc -l < "$LEAN_REPORT_MAKE_CALLS" | tr -d '[:space:]')" == "1" ]] \
    || fail "the next cycle rebuilt an already-valid report"
  [[ "$(wc -l < "$LEAN_REPORT_DOTNET_CALLS" | tr -d '[:space:]')" == "3" ]] \
    || fail "the next cycle reused an older report observation"
)

invalid_post_rebuild_report_fails_without_a_second_rebuild() (
  load_implementation || exit 1
  local root
  root="$(mktemp -d -t hourly-maintenance-invalid-post-report.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  mkdir -p "$root/bin" "$root/logs" "$root/slots"
  export FKST_MAINTENANCE_LOG="$root/logs/hourly-maintenance.log"
  export FKST_RESTART_ACTIVATION_STATE="$root/logs/restart-activation.state"
  export FKST_RESTART_DEFER_STATE="$root/logs/restart-defer.state"
  export FKST_REPORT_SLOT_ROOT="$root/slots"
  create_checkout_history_fixture "$root" || exit 1
  export FKST_HOST_ROOT="$CHECKOUT_ROOT"
  configure_lean_report_reconciliation_fixture "$root"
  export LEAN_REPORT_REBUILD_LEAVES_INVALID=1
  stub_report_cycle_dependencies

  main --host-config "$root/host.env" \
    && fail "an invalid post-rebuild report was reported as a successful cycle"

  [[ "$(wc -l < "$LEAN_REPORT_MAKE_CALLS" | tr -d '[:space:]')" == "1" ]] \
    || fail "a failed report postcondition triggered more than one rebuild"
  [[ "$(wc -l < "$LEAN_REPORT_DOTNET_CALLS" | tr -d '[:space:]')" == "2" ]] \
    || fail "failed report repair was not re-observed exactly once"
  command grep -q 'LEAN-REPORT-RECONCILE FAIL.*rebuilt report remains invalid' \
    "$FKST_MAINTENANCE_LOG" \
    || fail "invalid post-rebuild state was not reported loudly"
)

obligation_rebuild_is_not_repeated_by_invariant_reconciliation() (
  load_implementation || exit 1
  local root
  root="$(mktemp -d -t hourly-maintenance-obligation-once.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  mkdir -p "$root/bin" "$root/logs" "$root/slots"
  export FKST_MAINTENANCE_LOG="$root/logs/hourly-maintenance.log"
  export FKST_RESTART_ACTIVATION_STATE="$root/logs/restart-activation.state"
  export FKST_RESTART_DEFER_STATE="$root/logs/restart-defer.state"
  export FKST_REPORT_SLOT_ROOT="$root/slots"
  create_checkout_history_fixture "$root" || exit 1
  printf 'def obligationProbe : Nat := 1\n' > "$CHECKOUT_WRITER/ObligationProbe.lean"
  command git -C "$CHECKOUT_WRITER" add ObligationProbe.lean
  git_quiet -C "$CHECKOUT_WRITER" commit -m "advance obligation probe" || exit 1
  git_quiet -C "$CHECKOUT_WRITER" push origin dev || exit 1
  export FKST_HOST_ROOT="$CHECKOUT_ROOT"
  configure_lean_report_reconciliation_fixture "$root"
  stub_report_cycle_dependencies

  main --host-config "$root/host.env" \
    || fail "Lean obligation and invariant reconciliation should compose"

  [[ "$(wc -l < "$LEAN_REPORT_MAKE_CALLS" | tr -d '[:space:]')" == "1" ]] \
    || fail "the obligation rebuild was repeated by invariant reconciliation"
  [[ "$(wc -l < "$LEAN_REPORT_DOTNET_CALLS" | tr -d '[:space:]')" == "1" ]] \
    || fail "the obligation rebuild was not revalidated exactly once"
)

not_checked_report_status_fails_cycle_without_rebuild() (
  load_implementation || exit 1
  local root
  root="$(mktemp -d -t hourly-maintenance-report-not-checked.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  mkdir -p "$root/bin" "$root/logs" "$root/slots"
  export FKST_MAINTENANCE_LOG="$root/logs/hourly-maintenance.log"
  export FKST_RESTART_ACTIVATION_STATE="$root/logs/restart-activation.state"
  export FKST_RESTART_DEFER_STATE="$root/logs/restart-defer.state"
  export FKST_REPORT_SLOT_ROOT="$root/slots"
  create_checkout_history_fixture "$root" || exit 1
  export FKST_HOST_ROOT="$CHECKOUT_ROOT"
  configure_lean_report_reconciliation_fixture "$root"
  export LEAN_REPORT_PROBE_MODE=timeout
  stub_report_cycle_dependencies

  main --host-config "$root/host.env" \
    && fail "an unmeasured report state was reported as a successful cycle"

  [[ ! -e "$LEAN_REPORT_MAKE_CALLS" ]] \
    || fail "not-checked report state authorized a rebuild"
  command grep -q 'LEAN-REPORT-STATUS NOT CHECKED' "$FKST_MAINTENANCE_LOG" \
    || fail "not-checked report state was not preserved"
)

unrelated_digest_failure_does_not_authorize_report_rebuild() (
  load_implementation || exit 1
  local root
  root="$(mktemp -d -t hourly-maintenance-unrelated-digest.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  mkdir -p "$root/bin" "$root/logs" "$root/slots"
  export FKST_MAINTENANCE_LOG="$root/logs/hourly-maintenance.log"
  export FKST_RESTART_ACTIVATION_STATE="$root/logs/restart-activation.state"
  export FKST_RESTART_DEFER_STATE="$root/logs/restart-defer.state"
  export FKST_REPORT_SLOT_ROOT="$root/slots"
  create_checkout_history_fixture "$root" || exit 1
  export FKST_HOST_ROOT="$CHECKOUT_ROOT"
  configure_lean_report_reconciliation_fixture "$root"
  export LEAN_REPORT_PROBE_MODE=digest-failure
  stub_report_cycle_dependencies

  main --host-config "$root/host.env" \
    && fail "untyped aggregate failure was reported as a successful report check"

  [[ ! -e "$LEAN_REPORT_MAKE_CALLS" ]] \
    || fail "an unrelated ledger/CAS failure authorized make lean-report"
  command grep -q 'LEAN-REPORT-STATUS NOT CHECKED' "$FKST_MAINTENANCE_LOG" \
    || fail "untyped aggregate failure was not kept distinct from report invalidity"
)
