#!/bin/bash
set -euo pipefail
MODE="${MODE:-push}"
BASE_SHA="${BASE:-}"
ROOT=""
CANDIDATE=""
TEMPORARY=""
stage="input"
reason=""
finish() {
  local raw=$?
  trap - EXIT
  set +e
  local rc=2
  case "$raw" in 0|1|2) rc="$raw" ;; esac
  if [[ -n "$ROOT" ]] && declare -F resource_observe >/dev/null; then resource_observe preflight-finish "$ROOT" || true; fi
  if [[ -n "$TEMPORARY" && -d "$CANDIDATE/build/ci" ]]; then
    local retained="$ROOT/build/preflight"
    mkdir -p "$retained" || rc=2
    local bundle
    bundle="$(mktemp "$retained/candidate.XXXXXXXX")" || rc=2
    # Current includes the shared runtime and report; engineering's records and
    # failure diagnostics live under build/ci. Archive each common member once.
    local paths="$CANDIDATE/build/ci/current-paths.nul"
    [[ -f "$paths" ]] || paths="$CANDIDATE/build/ci/build-paths.nul"
    if [[ -f "$paths" ]]; then
      while IFS= read -r -d '' path; do
        case "$path" in build/ci|build/ci/*) ;; *) printf '%s\0' "$path" ;; esac
      done < "$paths" > "$TEMPORARY/artifact-paths.nul"
      printf 'build/ci\0' >> "$TEMPORARY/artifact-paths.nul"
      tar -czf "$bundle" -C "$CANDIDATE" --null -T "$TEMPORARY/artifact-paths.nul" || rc=2
    else
      tar -czf "$bundle" -C "$CANDIDATE" build/ci || rc=2
    fi
    printf 'PREFLIGHT_ARTIFACT bundle=%s\n' "$bundle"
  fi
  if [[ -n "$TEMPORARY" ]]; then rm -rf -- "$TEMPORARY"; fi
  printf 'PREFLIGHT_RESULT mode=%s stage=%s exit=%s raw_exit=%s reason=%s\n' "$MODE" "$stage" "$rc" "$raw" "$reason"
  exit "$rc"
}
trap finish EXIT
trap 'reason=interrupted; exit 2' HUP INT TERM
fail_input() { reason="$1"; exit 2; }
case "$MODE" in push|pr) ;; *) MODE=invalid; fail_input invalid-mode ;; esac
ROOT="$(git rev-parse --show-toplevel)" || fail_input invalid-repository
cd "$ROOT"
CANDIDATE="$ROOT"
if [[ "$MODE" == pr ]]; then
  [[ "$BASE_SHA" =~ ^[0-9a-fA-F]{40}$ ]] || fail_input invalid-base-sha
  [[ "$(git cat-file -t "$BASE_SHA" 2>/dev/null)" == commit ]] || fail_input unavailable-base-commit
  status_output="$(git status --porcelain --untracked-files=all)" || fail_input status-observation-failed
  [[ -z "$status_output" ]] || fail_input dirty-tree
  HEAD_SHA="$(git rev-parse --verify 'HEAD^{commit}')" || fail_input uncommitted-head
  stage=merge-tree
  merge_rc=0
  merge_output="$(git merge-tree --write-tree "$BASE_SHA" "$HEAD_SHA" 2>&1)" || merge_rc=$?
  if [[ "$merge_rc" != 0 ]]; then
    printf '%s\n' "$merge_output" >&2
    reason=merge-failed
    [[ "$merge_rc" == 1 ]] && exit 1
    exit 2
  fi
  TREE_SHA="${merge_output%%$'\n'*}"
  [[ "$TREE_SHA" =~ ^[0-9a-fA-F]{40}$ ]] || fail_input invalid-merge-tree
  TEMPORARY="$(mktemp -d "${TMPDIR:-/tmp}/ci-preflight.XXXXXXXX")"
  CANDIDATE="$TEMPORARY/candidate"
  git clone --quiet --shared --no-checkout "$ROOT" "$CANDIDATE"
  git -C "$CANDIDATE" read-tree --reset -u "$TREE_SHA"
  printf 'PREFLIGHT_CANDIDATE path=%s\n' "$CANDIDATE"
fi
if [[ -f "$ROOT/tools/scripts/lib/resource-observation-lib.sh" ]]; then
  source "$ROOT/tools/scripts/lib/resource-observation-lib.sh"
  resource_observe preflight-start "$CANDIDATE" || true
fi
cd "$CANDIDATE"
for stage in engineering current; do
  /bin/bash tools/scripts/ci-stage.sh "$stage"
done
if [[ "$MODE" == pr ]]; then
  stage=delta
  /bin/bash tools/scripts/ci-stage.sh delta "$BASE_SHA"
fi
stage=complete
