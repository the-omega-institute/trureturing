#!/usr/bin/env bash

admission_base_resolution_failure() {
  local reason="$1"
  local base_ref="$2"
  local base_tip_sha="$3"
  local candidate_sha="$4"
  local base_sha="$5"

  printf 'BASE_RESOLUTION_FAILED reason=%s BASE_REF=%s BASE_TIP_SHA=%s CANDIDATE_SHA=%s BASE_SHA=%s\n' \
    "$reason" "${base_ref:-empty}" "${base_tip_sha:-empty}" \
    "${candidate_sha:-empty}" "${base_sha:-empty}" >&2
}

admission_resolve_base() {
  local repository_root="$1"
  local base_ref="$2"
  local resolution_rc=0
  local resolution_reason=""

  CANDIDATE_SHA=""
  BASE_TIP_SHA=""
  BASE_SHA=""

  CANDIDATE_SHA="$(git -C "$repository_root" rev-parse --verify "HEAD^{commit}")" \
    || resolution_rc=$?
  if [[ "$resolution_rc" -ne 0 || -z "$CANDIDATE_SHA" ]]; then
    admission_base_resolution_failure \
      candidate-resolution-failed "$base_ref" "$BASE_TIP_SHA" "$CANDIDATE_SHA" "$BASE_SHA"
    return 1
  fi

  resolution_rc=0
  BASE_TIP_SHA="$(git -C "$repository_root" rev-parse --verify "${base_ref}^{commit}")" \
    || resolution_rc=$?
  if [[ "$resolution_rc" -ne 0 || -z "$BASE_TIP_SHA" ]]; then
    admission_base_resolution_failure \
      base-tip-resolution-failed "$base_ref" "$BASE_TIP_SHA" "$CANDIDATE_SHA" "$BASE_SHA"
    return 1
  fi

  resolution_rc=0
  BASE_SHA="$(git -C "$repository_root" merge-base "$BASE_TIP_SHA" "$CANDIDATE_SHA")" \
    || resolution_rc=$?
  if [[ "$resolution_rc" -ne 0 ]]; then
    resolution_reason="merge-base-command-failed"
  elif [[ -z "$BASE_SHA" || "$BASE_SHA" =~ ^0+$ ]]; then
    resolution_reason="merge-base-empty"
  elif [[ "$BASE_SHA" == "$CANDIDATE_SHA" ]]; then
    resolution_reason="vacuous"
  fi

  if [[ -n "$resolution_reason" ]]; then
    admission_base_resolution_failure \
      "$resolution_reason" "$base_ref" "$BASE_TIP_SHA" "$CANDIDATE_SHA" "$BASE_SHA"
    return 1
  fi
}

# ci payload: touches tools/ so base_full_required=true, exercising the protected-base FULL path
# on the integration base for issue #4399. Delete with the integration branch.
