#!/bin/bash
# Entry step of every CI workflow: verify the event candidate, decide whether
# this unit's registered input patterns are hit, then drop remote state.
# Environment: exactly one of CI_HIT_PATHS or CI_HIT_PATHS_FILE (a readable file
# containing the same text: one bash pattern per line; `*` also matches `/`;
# a leading `!` excludes; blank lines and `#` lines are ignored; a path hits
# when it matches an including pattern and no excluding one), GITHUB_EVENT_NAME, GITHUB_SHA,
# GITHUB_OUTPUT, CI_PR_HEAD (pull_request), CI_PUSH_BEFORE (push), and optionally
# CI_CHANGED_PATHS_FILE, which receives the NUL-separated changed paths whenever
# a base commit exists and is removed otherwise.
# Output: hit=true|false in GITHUB_OUTPUT. Pull requests compare the event's
# merge commit M with its first parent B; pushes compare event.before with the
# pushed commit. A push range that cannot be read hits. Any other failure
# exits 2 so the job is red, never silently skipped.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../../.."

ZERO=0000000000000000000000000000000000000000
fail() { echo "CI_ENTRY_ERROR $*" >&2; exit 2; }
finish() {
  local hit="$1" reason="$2" remotes refs remote ref
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
  echo "CI_HIT hit=$hit reason=$reason"
  exit 0
}

[[ "${CI_HIT_PATHS+x}${CI_HIT_PATHS_FILE+x}" == x ]] || fail "set exactly one of CI_HIT_PATHS or CI_HIT_PATHS_FILE"
if [[ "${CI_HIT_PATHS_FILE+x}" == x ]]; then
  [[ -f "$CI_HIT_PATHS_FILE" && -r "$CI_HIT_PATHS_FILE" ]] || fail "cannot read CI_HIT_PATHS_FILE"
  hit_paths="$(cat -- "$CI_HIT_PATHS_FILE")" || fail "cannot read CI_HIT_PATHS_FILE"
else
  hit_paths="$CI_HIT_PATHS"
fi
include=() exclude=()
while IFS= read -r line; do
  line="${line#"${line%%[![:space:]]*}"}"
  line="${line%"${line##*[![:space:]]}"}"
  [[ -z "$line" || "$line" == \#* ]] && continue
  if [[ "$line" == !* ]]; then exclude+=("${line#!}"); else include+=("$line"); fi
done <<< "$hit_paths"
[[ ${#include[@]} -gt 0 ]] || fail "hit paths have no including pattern"
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
    [[ "$base" != "$ZERO" ]] || finish true new-branch
    if ! git cat-file -e "$base^{commit}" 2>/dev/null; then
      git fetch --quiet --no-tags --depth=1 origin "$base" 2>/dev/null || finish true before-unavailable
    fi
    ;;
  *) finish true "event-${GITHUB_EVENT_NAME:-unknown}" ;;
esac

# shellcheck disable=SC2053 # right-hand sides are patterns on purpose
excluded() {
  local pattern
  for pattern in ${exclude[@]+"${exclude[@]}"}; do [[ "$1" == $pattern ]] && return 0; done
  return 1
}

changes="$(mktemp)"
git diff --name-only --no-renames -z "$base" "$head" > "$changes" || fail "cannot diff $base..$head"
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
rm -f "$changes"

if [[ $matched -gt 0 ]]; then finish true "matched=$matched changed=$changed"; fi
finish false "matched=0 changed=$changed"
