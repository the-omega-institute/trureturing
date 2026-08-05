# Lean-report rebuild cases sourced by hourly-maintenance-behavior.sh.

already_stale_current_checkout_rebuilds_report() (
  load_implementation || exit 1
  local root make_calls probe_calls status_script verdict
  root="$(mktemp -d -t hourly-maintenance-stale-lean-report.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  mkdir -p \
    "$root/bin" \
    "$root/logs" \
    "$root/slots"
  LOG_FILE="$root/logs/hourly-maintenance.log"
  export FKST_MAINTENANCE_LOG="$LOG_FILE"
  export FKST_RESTART_ACTIVATION_STATE="$root/logs/restart-activation.state"
  export FKST_RESTART_DEFER_STATE="$root/logs/restart-defer.state"
  export FKST_REPORT_SLOT_ROOT="$root/slots"
  create_checkout_history_fixture "$root" || exit 1
  mkdir -p \
    "$CHECKOUT_ROOT/.claude/skills/fkst-monitor/scripts" \
    "$CHECKOUT_ROOT/Meta/StrataLint/StrataLint.Cli"
  touch "$CHECKOUT_ROOT/Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj"
  status_script="$CHECKOUT_ROOT/.claude/skills/fkst-monitor/scripts/status.sh"
  command cp \
    "$REPOSITORY_ROOT/.claude/skills/fkst-monitor/scripts/status.sh" \
    "$status_script"
  export FKST_HOST_ROOT="$CHECKOUT_ROOT"
  export REPORT_READY="$root/report-ready"
  make_calls="$root/make.calls"
  probe_calls="$root/probe.calls"
  export MAKE_CALLS="$make_calls" PROBE_CALLS="$probe_calls"
  cat > "$root/bin/make" <<'SH'
#!/usr/bin/env bash
printf '%s\n' "$*" >> "$MAKE_CALLS"
[[ "$*" == "-C $FKST_HOST_ROOT lean-report" ]] || exit 97
: > "$REPORT_READY"
SH
  cat > "$root/bin/dotnet" <<'SH'
#!/usr/bin/env bash
printf '%s\n' "$PWD|$*" >> "$PROBE_CALLS"
if [[ -e "$REPORT_READY" ]]; then
  printf '{"schema":"stratalint-formalize-candidates-v3","candidates":[],"recorded_formalizations":[],"withheld":[]}\n'
  exit 0
fi
printf 'DIGEST_STATUS_INVALID Raw Lean report is missing modules: D5/Stale.lean\n' >&2
exit 1
SH
  chmod +x "$root/bin/make" "$root/bin/dotnet"
  export FKST_MAKE_BIN="$root/bin/make"
  export PATH="$root/bin:$PATH"

  host_contract_load() { return 0; }
  validate_configuration() { return 0; }
  host_contract_require() { return 0; }
  sync_platform() { return 0; }
  sync_workspace_composition() { return 0; }
  gc_worktrees() { return 0; }
  gc_stuck_lean_builds() { return 0; }
  check_launchd_conformance() { return 0; }

  main --host-config "$root/host.env" \
    || fail "already-current stale checkout was not reconciled"
  [[ -e "$REPORT_READY" ]] \
    || fail "already-current stale checkout still had an unusable Lean report after the cycle"
  [[ "$(<"$make_calls")" == "-C $CHECKOUT_ROOT lean-report" ]] \
    || fail "stale checkout did not rebuild exactly once through make lean-report"
  [[ "$(wc -l < "$probe_calls" | tr -d '[:space:]')" == "1" ]] \
    || fail "maintenance ran the bounded readiness probe more than once"
  command grep -q 'LEAN-REPORT-RECONCILE OK' "$LOG_FILE" \
    || fail "successful stale-report reconciliation was not reported"

  verdict="$(
    FKST_FORMALIZE_CHECKOUT="$CHECKOUT_ROOT" \
      bash "$status_script" --formalize-readiness
  )" || fail "rebuilt report was not valid according to the canonical readiness verdict"
  [[ "$verdict" == "ready" ]] \
    || fail "rebuilt report verdict was not ready: $verdict"
)

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

  sync_checkout || fail "Lean-changing checkout sync should succeed"
  command grep -q '^lean_report_required=1$' "$obligation" \
    || fail "Lean-changing fast-forward did not persist its report obligation before mutation"
  restart_engine() {
    [[ -s "$make_calls" ]] || fail "restart began before the Lean report was rebuilt"
  }
  engine_pid() { return 0; }

  restart_if_needed || fail "successful Lean report rebuild should reconcile activation"
  reconcile_lean_report_readiness \
    || fail "obligation rebuild should satisfy the final readiness reconciliation"
  [[ "$(<"$make_calls")" == "-C $CHECKOUT_ROOT lean-report" ]] \
    || fail "maintenance did not delegate rebuild to make lean-report: $(<"$make_calls")"
  [[ ! -e "$obligation" ]] \
    || fail "successful rebuild and restart did not clear the activation obligation"
  command grep -q 'LEAN-REPORT-REBUILD OK' "$LOG_FILE" \
    || fail "successful report obligation discharge was not reported"
  command grep -q 'LEAN-REPORT-RECONCILE SATISFIED' "$LOG_FILE" \
    || fail "final reconciliation did not reuse the obligation rebuild"
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
