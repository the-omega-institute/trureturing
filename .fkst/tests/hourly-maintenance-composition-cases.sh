# Workspace-composition cases sourced by hourly-maintenance-behavior.sh.

write_composition_workspace() {
  local path="$1" rev="$2" packages="$3" libraries="$4" units="$5" marker="$6"
  mkdir -p "$(dirname -- "$path")"
  {
    printf '[workspace]\n'
    printf 'units = [%s]\n\n' "$units"
    printf '[[external_sources]]\n'
    printf 'id = "fkst-packages-platform"\n'
    printf 'git = "https://github.com/ChronoAIProject/fkst-packages.git"\n'
    printf 'rev = "%s"\n' "$rev"
    printf 'packages = [%s]\n' "$packages"
    printf 'libraries = [%s]\n' "$libraries"
    printf 'runtime_marker = "%s"\n' "$marker"
  } > "$path"
}

create_composition_cycle_fixture() {
  local root="$1" tracked_packages="$2" runtime_packages="$3"
  create_platform_fixture "$root" || return 1

  CHECKOUT_REMOTE="$root/checkout-remote.git"
  CHECKOUT_ROOT="$root/checkout"
  CHECKOUT_WRITER="$root/checkout-writer"
  git_quiet init --bare --initial-branch=dev "$CHECKOUT_REMOTE" || return 1
  git_quiet clone "$CHECKOUT_REMOTE" "$CHECKOUT_ROOT" || return 1
  configure_repository "$CHECKOUT_ROOT" || return 1
  write_composition_workspace \
    "$CHECKOUT_ROOT/.fkst/fkst.workspace.toml" \
    "$OLD_PLATFORM_REV" \
    "$tracked_packages" \
    '"contract", "workflow"' \
    '"packages/host-a"' \
    tracked
  printf 'base\n' > "$CHECKOUT_ROOT/tracked"
  command git -C "$CHECKOUT_ROOT" add .fkst/fkst.workspace.toml tracked
  git_quiet -C "$CHECKOUT_ROOT" commit -m base || return 1
  git_quiet -C "$CHECKOUT_ROOT" push -u origin dev || return 1
  git_quiet clone "$CHECKOUT_REMOTE" "$CHECKOUT_WRITER" || return 1
  configure_repository "$CHECKOUT_WRITER" || return 1

  write_composition_workspace \
    "$CHECKOUT_ROOT/fkst.workspace.toml" \
    "$NEW_PLATFORM_REV" \
    "$runtime_packages" \
    '"legacy-library"' \
    '"packages/legacy-host"' \
    keep-runtime
  printf 'synthetic-lock\n' > "$CHECKOUT_ROOT/fkst.lock"
  mkdir -p "$root/bin" "$root/logs" "$root/worktrees" "$root/slots"
  LOG_FILE="$root/logs/hourly-maintenance.log"
  export FKST_HOST_ROOT="$CHECKOUT_ROOT"
  export FKST_PLATFORM_ROOT="$PLATFORM_ROOT"
  export FKST_MAINTENANCE_LOG="$LOG_FILE"
  export FKST_WORKTREE_ROOT="$root/worktrees"
  export FKST_REPORT_SLOT_ROOT="$root/slots"
  export FKST_GITHUB_REPO="example/synthetic"
  export FKST_LAUNCHD_LABEL="com.example.synthetic-fkst"
  export FKST_PYTHON_BIN
  FKST_PYTHON_BIN="$(command -v python3)"
  export FKST_MAKE_BIN="$root/bin/make"
  export FKST_RUN_SCRIPT="$root/bin/run-engine"
  cat > "$FKST_RUN_SCRIPT" <<SH
#!/usr/bin/env bash
printf 'restart attempted\n' >> "$root/restart.calls"
SH
  cat > "$FKST_MAKE_BIN" <<'SH'
#!/usr/bin/env bash
printf '%s\n' "$*" >> "$FKST_COMPOSITION_GATE_CALLS"
"$FKST_PYTHON_BIN" - "$FKST_HOST_ROOT/.fkst/fkst.workspace.toml" \
  "$FKST_HOST_ROOT/fkst.workspace.toml" <<'PY'
import sys
import tomllib


def load(path):
    with open(path, "rb") as handle:
        return tomllib.load(handle)


def composition(manifest):
    source = [
        item for item in manifest["external_sources"]
        if item.get("id") == "fkst-packages-platform"
    ]
    if len(source) != 1:
        raise SystemExit("fixture gate expected one platform source")
    return {
        "packages": set(source[0]["packages"]),
        "libraries": set(source[0]["libraries"]),
        "units": set(manifest["workspace"]["units"]),
    }


if composition(load(sys.argv[1])) != composition(load(sys.argv[2])):
    raise SystemExit("fixture composition gate: runtime differs from tracked")
PY
SH
  chmod +x "$FKST_RUN_SCRIPT" "$FKST_MAKE_BIN"
  export FKST_COMPOSITION_GATE_CALLS="$root/gate.calls"

  host_contract_load() {
    HOST_CONFIG="$1"
    export HOST_CONFIG
  }
  validate_configuration() { return 0; }
  host_contract_require() { return 0; }
  gc_worktrees() { return 0; }
  gc_stuck_lean_builds() { return 0; }
  reconcile_lean_report_invariant() { return 0; }
}

advance_tracked_composition() {
  local packages="$1"
  write_composition_workspace \
    "$CHECKOUT_WRITER/.fkst/fkst.workspace.toml" \
    "$OLD_PLATFORM_REV" \
    "$packages" \
    '"contract", "workflow"' \
    '"packages/host-a"' \
    tracked
  command git -C "$CHECKOUT_WRITER" add .fkst/fkst.workspace.toml
  git_quiet -C "$CHECKOUT_WRITER" commit -m "advance composition" || return 1
  git_quiet -C "$CHECKOUT_WRITER" push origin dev || return 1
}

assert_runtime_composition() {
  local root="$1" packages="$2" expected_rev="$3"
  "$FKST_PYTHON_BIN" - \
    "$root/checkout/fkst.workspace.toml" "$packages" "$expected_rev" <<'PY'
import sys
import tomllib

with open(sys.argv[1], "rb") as handle:
    manifest = tomllib.load(handle)
source = next(
    item for item in manifest["external_sources"]
    if item["id"] == "fkst-packages-platform"
)
expected = set(filter(None, sys.argv[2].split(",")))
assert set(source["packages"]) == expected
assert set(source["libraries"]) == {"contract", "workflow"}
assert set(manifest["workspace"]["units"]) == {"packages/host-a"}
assert source["rev"] == sys.argv[3]
assert source["runtime_marker"] == "keep-runtime"
PY
}

tracked_package_removal_propagates_after_checkout_fast_forward() (
  load_implementation || exit 1
  local root output
  root="$(mktemp -d -t hourly-maintenance-composition-remove.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  create_composition_cycle_fixture "$root" '"alpha", "obsolete"' '"alpha", "obsolete"' \
    || exit 1
  advance_tracked_composition '"alpha"' || exit 1
  restart_if_needed() { return 0; }
  output="$root/output"

  main --host-config "$root/host.env" >"$output" 2>&1 \
    || fail "package-removal cycle failed: $(<"$output")"
  assert_runtime_composition "$root" alpha "$NEW_PLATFORM_REV" \
    || fail "runtime did not adopt the tracked package removal"
  [[ -s "$FKST_COMPOSITION_GATE_CALLS" ]] \
    || fail "composition gate did not run after package removal"
)

tracked_package_addition_propagates_after_checkout_fast_forward() (
  load_implementation || exit 1
  local root output
  root="$(mktemp -d -t hourly-maintenance-composition-add.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  create_composition_cycle_fixture "$root" '"alpha"' '"alpha"' || exit 1
  advance_tracked_composition '"alpha", "new-package"' || exit 1
  restart_if_needed() { return 0; }
  output="$root/output"

  main --host-config "$root/host.env" >"$output" 2>&1 \
    || fail "package-addition cycle failed: $(<"$output")"
  assert_runtime_composition "$root" alpha,new-package "$NEW_PLATFORM_REV" \
    || fail "runtime did not adopt the tracked package addition"
  [[ -s "$FKST_COMPOSITION_GATE_CALLS" ]] \
    || fail "composition gate did not run after package addition"
)

platform_current_cycle_still_propagates_composition() (
  load_implementation || exit 1
  local root output
  root="$(mktemp -d -t hourly-maintenance-composition-current.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  create_composition_cycle_fixture "$root" '"alpha"' '"stale"' || exit 1
  restart_if_needed() { return 0; }
  output="$root/output"

  main --host-config "$root/host.env" >"$output" 2>&1 \
    || fail "platform-current propagation cycle failed: $(<"$output")"
  command grep -q 'PLATFORM CURRENT' "$output" \
    || fail "fixture did not exercise PLATFORM CURRENT"
  assert_runtime_composition "$root" alpha "$NEW_PLATFORM_REV" \
    || fail "PLATFORM CURRENT skipped composition propagation"
)

post_write_composition_drift_fails_closed_with_differences() (
  load_implementation || exit 1
  local root output real_mv
  root="$(mktemp -d -t hourly-maintenance-composition-drift.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  create_composition_cycle_fixture "$root" '"alpha"' '"stale"' || exit 1
  output="$root/output"
  real_mv="$(command -v mv)"
  export REAL_MV="$real_mv"
  export COMPOSITION_INJECTION_TARGET="$CHECKOUT_ROOT/fkst.workspace.toml"
  cat > "$root/bin/mv" <<'SH'
#!/usr/bin/env bash
"$REAL_MV" "$@" || exit
if [[ "${!#}" == "$COMPOSITION_INJECTION_TARGET" ]]; then
  perl -0pi -e 's/packages = \["alpha"\]/packages = ["alpha", "injected"]/' \
    "$COMPOSITION_INJECTION_TARGET"
fi
SH
  chmod +x "$root/bin/mv"
  export PATH="$root/bin:$PATH"
  restart_if_needed() { return 0; }

  if main --host-config "$root/host.env" >"$output" 2>&1; then
    fail "post-write composition mismatch did not fail the maintenance cycle"
  fi
  command grep -q \
    'WORKSPACE-COMPOSITION-DRIFT: packages only-in-tracked=\[\] only-in-runtime=\[injected\]' \
    "$output" \
    || fail "composition failure did not identify the package difference: $(<"$output")"
  [[ ! -e "$FKST_COMPOSITION_GATE_CALLS" ]] \
    || fail "downstream gate ran after composition verification failed"
)

composition_only_propagation_does_not_trigger_restart() (
  load_implementation || exit 1
  local root output second_output
  root="$(mktemp -d -t hourly-maintenance-composition-no-restart.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  create_composition_cycle_fixture "$root" '"alpha"' '"stale"' || exit 1
  output="$root/output"

  main --host-config "$root/host.env" >"$output" 2>&1 \
    || fail "composition-only cycle failed: $(<"$output")"
  assert_runtime_composition "$root" alpha "$NEW_PLATFORM_REV" \
    || fail "composition-only cycle did not propagate"
  [[ ! -e "$root/restart.calls" ]] \
    || fail "composition-only propagation attempted an engine restart"
  command grep -q 'ALL CURRENT; no restart' "$output" \
    || fail "composition-only propagation changed restart policy: $(<"$output")"

  command cp "$CHECKOUT_ROOT/fkst.workspace.toml" "$root/workspace.after-first-cycle"
  second_output="$root/second-output"
  main --host-config "$root/host.env" >"$second_output" 2>&1 \
    || fail "second composition-only cycle failed: $(<"$second_output")"
  command cmp -s "$root/workspace.after-first-cycle" "$CHECKOUT_ROOT/fkst.workspace.toml" \
    || fail "idempotent composition cycle rewrote the runtime workspace"
  command grep -q 'WORKSPACE COMPOSITION CURRENT' "$second_output" \
    || fail "idempotent composition cycle was not reported as current"
  [[ ! -e "$root/restart.calls" ]] \
    || fail "idempotent composition cycle attempted an engine restart"
)
