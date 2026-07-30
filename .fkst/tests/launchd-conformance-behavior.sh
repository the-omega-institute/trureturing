#!/usr/bin/env bash
set -uo pipefail

REPOSITORY_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd -P)"
CHECKER="$REPOSITORY_ROOT/.fkst/scripts/check-launchd-conformance.sh"
PASSED=0
FAILED=0
SCRATCH=""

pass() {
  PASSED=$((PASSED + 1))
  printf 'ok %d - %s\n' "$((PASSED + FAILED))" "$1"
}

fail() {
  FAILED=$((FAILED + 1))
  printf 'not ok %d - %s\n' "$((PASSED + FAILED))" "$1"
}

run_checker() {
  local scratch="$1" host_config="$2" mode="$3" output="$4"
  FAKE_LAUNCHD_MODE="$mode" \
  FAKE_MAKE_LOG="$scratch/make.log" \
  FKST_LAUNCHD_ENUMERATOR="$scratch/bin/launchd-enumerator" \
  FKST_MAKE_BIN="$scratch/bin/make" \
  HOST_CONFIG="$host_config" \
    /bin/bash "$CHECKER" > "$output" 2>&1
}

assert_enumerator_failure_is_rejected() {
  local scratch="$1" host_config="$2" output="$scratch/enumerator-failure.out"
  if run_checker "$scratch" "$host_config" failure "$output"; then
    return 1
  fi
  grep -Fq 'launchd-conformance-check: launchd membership enumerator failed with exit 23' "$output"
}

assert_ungrounded_empty_membership_is_rejected() {
  local scratch="$1" host_config="$2" output="$scratch/empty-membership.out"
  if run_checker "$scratch" "$host_config" empty "$output"; then
    return 1
  fi
  grep -Fq 'launchd-conformance-check: no launchd units found for deployment namespace' "$output"
}

assert_host_only_member_is_rejected() {
  local scratch="$1" host_config="$2" output="$scratch/host-only.out"
  if run_checker "$scratch" "$host_config" host-only "$output"; then
    return 1
  fi
  grep -Fq 'launchd-conformance-check: launchd unit worker is absent from operational inventory' "$output"
}

assert_declared_members_are_checked() {
  local scratch="$1" host_config="$2" output="$scratch/conformant.out"
  : > "$scratch/make.log"
  run_checker "$scratch" "$host_config" conformant "$output" \
    && grep -Fq 'maintenance-launcher-check' "$scratch/make.log" \
    && grep -Fq 'supervise-launcher-check' "$scratch/make.log" \
    && grep -Fq 'launchd-conformance-check: conformant units: maintenance supervise' "$output"
}

write_host_config() {
  local scratch="$1" host_config="$2" python_bin="$3"
  mkdir -p \
    "$scratch/checkout/.fkst" \
    "$scratch/durable" \
    "$scratch/logs" \
    "$scratch/platform" \
    "$scratch/rate-pool" \
    "$scratch/report-slots" \
    "$scratch/runtime" \
    "$scratch/workflows" \
    "$scratch/worktrees"
  cp "$REPOSITORY_ROOT/.fkst/deploy.env" "$scratch/checkout/.fkst/deploy.env"
  cat > "$host_config" <<EOF
BIN=$scratch/fkst-framework
FKST_BASH_BIN=/bin/bash
FKST_ZSH_BIN=/bin/zsh
FKST_PYTHON_BIN=$python_bin
FKST_HOST_ROOT=$scratch/checkout
FKST_PLATFORM_ROOT=$scratch/platform
FKST_DURABLE_ROOT=$scratch/durable
FKST_RUNTIME_ROOT=$scratch/runtime
FKST_RATE_POOL_ROOT=$scratch/rate-pool
FKST_WORKFLOW_CATALOG_ROOT=$scratch/workflows
PATH=/usr/bin:/bin
FKST_GITHUB_BOT_LOGIN=synthetic-bot
FKST_DEVLOOP_MANAGED_BOT_LOGINS=synthetic-bot
FKST_DEVLOOP_INTEGRATION_BRANCH=integration-synthetic
FKST_RUN_SCRIPT=$scratch/checkout/.fkst/scripts/run.sh
FKST_MAINTENANCE_LOG=$scratch/logs/hourly-maintenance.log
FKST_MAINTENANCE_LAUNCHER_LOG=$scratch/logs/maintenance-launchd.log
FKST_WORKTREE_ROOT=$scratch/worktrees
FKST_REPORT_SLOT_ROOT=$scratch/report-slots
FKST_TIMEOUT_BIN=/usr/bin/timeout
FKST_LAUNCHD_LABEL=local.fkst.synthetic.supervise
FKST_MAINTENANCE_LAUNCHD_LABEL=local.fkst.synthetic.maintenance
FKST_MAINTENANCE_LAUNCHER_PATH=$scratch/local.fkst.synthetic.maintenance.plist
FKST_SUPERVISE_LAUNCHER_LOG=$scratch/logs/supervise-launchd.log
FKST_SUPERVISE_LAUNCHER_PATH=$scratch/local.fkst.synthetic.supervise.plist
source "\$FKST_HOST_ROOT/.fkst/deploy.env"
EOF
}

write_fakes() {
  local scratch="$1"
  mkdir -p "$scratch/bin"
  cat > "$scratch/bin/launchd-enumerator" <<'SH'
#!/usr/bin/env bash
case "${FAKE_LAUNCHD_MODE:-}" in
  failure) exit 23 ;;
  empty) exit 0 ;;
  host-only)
    printf '%s\n' \
      local.fkst.synthetic.maintenance \
      local.fkst.synthetic.supervise \
      local.fkst.synthetic.worker
    ;;
  conformant)
    printf '%s\n' \
      local.fkst.synthetic.maintenance \
      local.fkst.synthetic.supervise
    ;;
  *) exit 24 ;;
esac
SH
  cat > "$scratch/bin/make" <<'SH'
#!/usr/bin/env bash
printf '%s\n' "$*" >> "$FAKE_MAKE_LOG"
SH
  chmod +x "$scratch/bin/launchd-enumerator" "$scratch/bin/make"
}

main() {
  local scratch host_config python_bin
  scratch="$(mktemp -d -t launchd-conformance-behavior.XXXXXXXX)"
  SCRATCH="$scratch"
  trap 'rm -rf "$SCRATCH"' EXIT
  host_config="$scratch/host.env"
  python_bin="$(command -v python3)"
  write_host_config "$scratch" "$host_config" "$python_bin"
  write_fakes "$scratch"

  if assert_enumerator_failure_is_rejected "$scratch" "$host_config"; then
    pass 'launchd membership source failure is rejected'
  else
    fail 'launchd membership source failure is rejected'
  fi
  if assert_ungrounded_empty_membership_is_rejected "$scratch" "$host_config"; then
    pass 'ungrounded empty launchd membership is rejected'
  else
    fail 'ungrounded empty launchd membership is rejected'
  fi
  if assert_host_only_member_is_rejected "$scratch" "$host_config"; then
    pass 'host-only launchd member is rejected'
  else
    fail 'host-only launchd member is rejected'
  fi
  if assert_declared_members_are_checked "$scratch" "$host_config"; then
    pass 'declared host launchd members delegate to tracked byte checks'
  else
    fail 'declared host launchd members delegate to tracked byte checks'
  fi

  printf 'launchd conformance behavior tests: %d passed, %d failed, %d total\n' \
    "$PASSED" "$FAILED" "$((PASSED + FAILED))"
  [[ "$FAILED" -eq 0 ]]
}

main "$@"
