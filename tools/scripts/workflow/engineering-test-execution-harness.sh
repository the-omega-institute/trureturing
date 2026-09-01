#!/usr/bin/env bash
set -euo pipefail

if [[ "$#" -ne 2 || -z "$1" || -z "$2" ]]; then
  printf '%s\n' \
    'usage: engineering-test-execution-harness.sh <base-harness-root> <plan-file>' >&2
  exit 2
fi

base_harness_root="$1"
plan_file="$2"
: "${GITHUB_WORKSPACE:?}"
: "${ENGINEERING_HEAD:?}"
: "${ENGINEERING_BASE:?}"
: "${ENGINEERING_EXECUTION_FULL_REQUIRED:?}"
[[ "$ENGINEERING_EXECUTION_FULL_REQUIRED" == "true"
    || "$ENGINEERING_EXECUTION_FULL_REQUIRED" == "false" ]]

run_engineering_tests() {
  if [[ "$ENGINEERING_EXECUTION_FULL_REQUIRED" == "true" ]]; then
    FULL=1 make -C "$base_harness_root/tools" engineering-tests-base-cwd REPOSITORY="$GITHUB_WORKSPACE/candidate" MODE=plan HEAD="$ENGINEERING_HEAD" BASE="$ENGINEERING_BASE" PLAN_FILE="$plan_file"
  else
    make -C "$base_harness_root/tools" engineering-tests-base-cwd REPOSITORY="$GITHUB_WORKSPACE/candidate" MODE=plan HEAD="$ENGINEERING_HEAD" BASE="$ENGINEERING_BASE" PLAN_FILE="$plan_file"
  fi
  make -C "$base_harness_root/tools" engineering-tests-base-cwd REPOSITORY="$GITHUB_WORKSPACE/candidate" MODE=execute HEAD="$ENGINEERING_HEAD" BASE="$ENGINEERING_BASE" PLAN_FILE="$plan_file"
}

observation_bootstrap="$base_harness_root/tools/scripts/lib/resource-observation-bootstrap.sh"
observation_bootstrap_reason=""
observation_bootstrap_status=0
if [[ ! -e "$observation_bootstrap" ]]; then
  observation_bootstrap_reason=bootstrap-missing
elif [[ ! -f "$observation_bootstrap" ]]; then
  observation_bootstrap_reason=bootstrap-not-regular
elif [[ ! -r "$observation_bootstrap" ]]; then
  observation_bootstrap_reason=bootstrap-unreadable
elif ! bash -n "$observation_bootstrap" >/dev/null 2>&1; then
  observation_bootstrap_reason=bootstrap-syntax-error
else
  unset -f resource_observation_run_with_base_library 2>/dev/null || true
  source "$observation_bootstrap" || observation_bootstrap_status=$?
  if [[ "$observation_bootstrap_status" -ne 0 ]]; then
    observation_bootstrap_reason=bootstrap-source-nonzero
  elif ! declare -F resource_observation_run_with_base_library >/dev/null; then
    observation_bootstrap_reason=bootstrap-entrypoint-missing
  fi
fi
if [[ -n "$observation_bootstrap_reason" ]]; then
  printf 'RESOURCE_OBSERVATION_LOADER status=UNAVAILABLE reason=%s exit=%s path=%s\n' \
    "$observation_bootstrap_reason" "$observation_bootstrap_status" "$observation_bootstrap"
  run_engineering_tests
else
  resource_observation_run_with_base_library "$base_harness_root" run_engineering_tests
fi
