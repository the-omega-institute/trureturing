#!/bin/bash
# Entry step of every CI job: verify the event candidate, decide whether the
# given path patterns are hit, then drop remote state.
# Environment: CI_HIT_PATHS (one bash pattern per line; `*` also matches `/`;
# a leading `!` excludes; blank lines and `#` lines are ignored; a path hits
# when it matches an including pattern and no excluding one), GITHUB_EVENT_NAME, GITHUB_SHA,
# GITHUB_OUTPUT, CI_PR_HEAD (pull_request), CI_PUSH_BEFORE (push), and optionally
# CI_CHANGED_PATHS_FILE, which receives the NUL-separated changed paths.
# CI_EXPECTED_BASE carries the base already verified by detection.
# CI_PUSH_RANGE=candidate skips path selection for an already selected job.
# CI_PUSH_RANGE=optional preserves conservative routing for publication probes.
# Ordinary scope errors exit 2 without emitting a hit or a manifest.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../../.."

ZERO=0000000000000000000000000000000000000000
fail() { echo "CI_ENTRY_ERROR $*" >&2; exit 2; }
finish() {
  local hit="$1" reason="$2" selected_base="${3:-}" remotes refs remote ref
  if [[ "${CI_EXPECTED_BASE+x}" == x && "$selected_base" != "$CI_EXPECTED_BASE" ]]; then
    fail "candidate base differs from detection"
  fi
  # Checks use only the checked-out candidate and fixed objects (§9.5). Any
  # cleanup failure is red: the hit result is written only after it succeeds.
  remotes="$(git remote)" || fail "cannot enumerate remotes"
  while IFS= read -r remote; do
    [[ -n "$remote" ]] || continue
    git remote remove "$remote" || fail "cannot remove remote $remote"
  done <<< "$remotes"
  refs="$(git for-each-ref --format='%(refname)' refs/remotes)" || fail "cannot enumerate remote refs"
  while IFS= read -r ref; do
    [[ -n "$ref" ]] || continue
    git update-ref -d "$ref" || fail "cannot delete $ref"
  done <<< "$refs"
  echo "hit=$hit" >> "${GITHUB_OUTPUT:?GITHUB_OUTPUT is required}"
  echo "base=$selected_base" >> "$GITHUB_OUTPUT"
  echo "CI_HIT hit=$hit reason=$reason"
  exit 0
}

[[ "${CI_HIT_PATHS+x}" == x ]] || fail "CI_HIT_PATHS is required"
include=() exclude=()
while IFS= read -r line; do
  line="${line#"${line%%[![:space:]]*}"}"
  line="${line%"${line##*[![:space:]]}"}"
  [[ -z "$line" || "$line" == \#* ]] && continue
  if [[ "$line" == !* ]]; then exclude+=("${line#!}"); else include+=("$line"); fi
done <<< "$CI_HIT_PATHS"
[[ ${#include[@]} -gt 0 ]] || fail "CI_HIT_PATHS has no including pattern"
if [[ -n "${CI_CHANGED_PATHS_FILE:-}" ]]; then
  rm -f -- "$CI_CHANGED_PATHS_FILE" || fail "cannot clear $CI_CHANGED_PATHS_FILE"
fi
[[ "${GITHUB_SHA:-}" =~ ^[0-9a-f]{40}$ ]] || fail "GITHUB_SHA must be a 40-hex commit"
head="$(git rev-parse --verify HEAD)"
[[ "$head" == "$GITHUB_SHA" ]] || fail "checkout $head differs from event commit $GITHUB_SHA"

case "${GITHUB_EVENT_NAME:-}" in
  pull_request)
    parents="$(git show -s --format='%P' HEAD)"
    read -r base pr_head extra <<< "$parents"
    [[ -n "${pr_head:-}" && -z "${extra:-}" ]] || fail "pull request candidate is not a two-parent merge commit"
    [[ "$pr_head" == "${CI_PR_HEAD:-}" ]] || fail "merge candidate does not contain the triggering PR head"
    ;;
  push)
    base="${CI_PUSH_BEFORE:-}"
    [[ "$base" =~ ^[0-9a-f]{40}$ ]] || fail "push event requires a 40-hex before commit"
    push_range="${CI_PUSH_RANGE:-required}"
    case "$push_range" in
      candidate) finish true push-candidate ;;
      optional|required) ;;
      *) fail "invalid CI_PUSH_RANGE: $push_range" ;;
    esac
    if [[ "$base" == "$ZERO" ]]; then
      [[ "$push_range" != optional ]] || finish true new-branch
      if [[ "${CI_EXPECTED_BASE+x}" == x ]]; then
        base="$CI_EXPECTED_BASE"
      else
        base="$(python3 tools/scripts/workflow/ci_contract.py --new-branch --head "$head")" ||
          fail "cannot establish the introduced commit range for $head"
      fi
      [[ "$base" =~ ^[0-9a-f]{40}$ && "$base" != "$ZERO" ]] || fail "invalid new branch base"
    fi
    if ! git cat-file -e "$base^{commit}" 2>/dev/null &&
       ! git fetch --quiet --no-tags --depth=1 origin "$base"; then
      [[ "$push_range" != optional ]] || finish true before-unavailable
      fail "cannot fetch push base $base for $head"
    fi
    ;;
  *) finish true "event-${GITHUB_EVENT_NAME:-unknown}" ;;
esac

if [[ "${CI_EXPECTED_BASE+x}" == x && "$base" != "$CI_EXPECTED_BASE" ]]; then
  fail "candidate base differs from detection"
fi

# shellcheck disable=SC2053 # right-hand sides are patterns on purpose
excluded() {
  local pattern
  for pattern in ${exclude[@]+"${exclude[@]}"}; do [[ "$1" == $pattern ]] && return 0; done
  return 1
}

changes="$(mktemp)"
trap 'rm -f -- "$changes"' EXIT
python3 tools/scripts/workflow/ci_contract.py --base "$base" --head "$head" --output "$changes" || fail "cannot diff $base..$head"
if [[ -n "${CI_CHANGED_PATHS_FILE:-}" ]]; then
  cp -- "$changes" "$CI_CHANGED_PATHS_FILE" || fail "cannot write $CI_CHANGED_PATHS_FILE"
fi
changed=0 matched=0
while IFS= read -r -d '' path; do
  changed=$((changed + 1))
  excluded "$path" && continue
  for pattern in "${include[@]}"; do
    # shellcheck disable=SC2053
    if [[ "$path" == $pattern ]]; then
      matched=$((matched + 1))
      if [[ $matched -le 20 ]]; then echo "CI_HIT_PATH $path pattern=$pattern"; fi
      break
    fi
  done
done < "$changes"
if [[ $matched -gt 0 ]]; then finish true "matched=$matched changed=$changed" "$base"; fi
finish false "matched=0 changed=$changed" "$base"
