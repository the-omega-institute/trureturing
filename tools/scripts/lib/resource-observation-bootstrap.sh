#!/usr/bin/env bash

resource_observation_run_with_base_library() {
  local base_root="${1:-}"
  local library=""
  local source_status=0
  if [[ $# -lt 2 || -z "$base_root" ]]; then return 2; fi
  shift
  library="$base_root/tools/scripts/lib/resource-observation-lib.sh"

  if [[ ! -e "$library" ]]; then
    printf 'RESOURCE_OBSERVATION_LOADER status=UNAVAILABLE reason=missing path=%s\n' "$library"
    "$@"
    return $?
  fi
  if [[ ! -f "$library" ]]; then
    printf 'RESOURCE_OBSERVATION_LOADER status=UNAVAILABLE reason=not-regular path=%s\n' "$library"
    "$@"
    return $?
  fi
  if [[ ! -r "$library" ]]; then
    printf 'RESOURCE_OBSERVATION_LOADER status=UNAVAILABLE reason=unreadable path=%s\n' "$library"
    "$@"
    return $?
  fi
  if ! bash -n "$library" >/dev/null 2>&1; then
    printf 'RESOURCE_OBSERVATION_LOADER status=UNAVAILABLE reason=syntax-error path=%s\n' "$library"
    "$@"
    return $?
  fi

  unset -f resource_observe_run_periodic 2>/dev/null || true
  if source "$library"; then
    source_status=0
  else
    source_status=$?
  fi
  if [[ "$source_status" -ne 0 ]]; then
    unset -f resource_observe_run_periodic 2>/dev/null || true
    printf 'RESOURCE_OBSERVATION_LOADER status=UNAVAILABLE reason=source-nonzero exit=%s path=%s\n' \
      "$source_status" "$library"
    "$@"
    return $?
  fi
  if ! declare -F resource_observe_run_periodic >/dev/null; then
    printf 'RESOURCE_OBSERVATION_LOADER status=UNAVAILABLE reason=entrypoint-missing path=%s\n' "$library"
    "$@"
    return $?
  fi

  resource_observe_run_periodic "$@"
}
