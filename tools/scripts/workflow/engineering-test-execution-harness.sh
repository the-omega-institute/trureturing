#!/usr/bin/env bash
set -euo pipefail

if [[ "$#" -ne 1 || -z "$1" ]]; then
  printf '%s\n' \
    'usage: engineering-test-execution-harness.sh <candidate-root>' >&2
  exit 2
fi

candidate_root="$1"
if ! candidate_root="$(cd "$candidate_root" && pwd -P)"; then
  printf 'ENGINEERING_TEST_EXECUTION_FAILED reason=candidate-root-unavailable path=%s\n' \
    "$1" >&2
  exit 2
fi
if ! git -C "$candidate_root" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  printf 'ENGINEERING_TEST_EXECUTION_FAILED reason=candidate-root-not-git path=%s\n' \
    "$candidate_root" >&2
  exit 2
fi

head_sha="$(git -C "$candidate_root" rev-parse HEAD)"
base_sha="$(git -C "$candidate_root" rev-parse HEAD^1)"

run_engineering_tests() {
  make \
    --no-print-directory \
    -C "$candidate_root/tools" \
    engineering-tests \
    "REPOSITORY=$candidate_root" \
    "HEAD=$head_sha" \
    "BASE=$base_sha"
}

observation_library="$candidate_root/tools/scripts/lib/resource-observation-lib.sh"
observation_unavailable() {
  local reason="$1"
  local source_status="${2:-0}"
  printf 'RESOURCE_OBSERVATION_LOADER status=UNAVAILABLE reason=%s exit=%s path=%s\n' \
    "$reason" "$source_status" "$observation_library"
  run_engineering_tests
}

if [[ ! -e "$observation_library" ]]; then
  observation_unavailable missing
elif [[ ! -f "$observation_library" ]]; then
  observation_unavailable not-regular
elif [[ ! -r "$observation_library" ]]; then
  observation_unavailable unreadable
elif ! bash -n "$observation_library" >/dev/null 2>&1; then
  observation_unavailable syntax-error
else
  unset -f resource_observe_run_periodic 2>/dev/null || true
  observation_source_status=0
  source "$observation_library" || observation_source_status=$?
  if [[ "$observation_source_status" -ne 0 ]]; then
    unset -f resource_observe_run_periodic 2>/dev/null || true
    observation_unavailable source-nonzero "$observation_source_status"
  elif ! declare -F resource_observe_run_periodic >/dev/null; then
    observation_unavailable entrypoint-missing
  else
    resource_observe_run_periodic run_engineering_tests
  fi
fi
