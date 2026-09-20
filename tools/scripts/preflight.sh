#!/bin/bash
set -euo pipefail
MODE="${MODE:-}"
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
usage() {
  cat >&2 <<'USAGE'
Choose an explicit local preflight mode (there is no default):
  make preflight MODE=fast
    Quick .NET structure tests (make -C tools check-fast); no Lean/admission proof.
  make preflight MODE=push BASE=<40-hex-commit-sha>
    Registered checks for the complete BASE-to-worktree delta, including dirty/untracked files.
  make preflight MODE=pr BASE=<40-hex-commit-sha>
    Clean committed source; isolated merge candidate, shared checks and cross-tree delta.
  make preflight MODE=full
    Registered checks for the whole current input; normal caches/incremental builds remain valid.
Use fast for harness iteration, targeted make lean for Lean iteration, push for delta validation,
pr for integration, and full for deliberate whole-tree diagnostics. fast/full reject BASE;
only push accepts a matching complete CI_PUSH_BEFORE/CI_PUSH_AFTER pair. No positional arguments.
USAGE
}
fail_input() { reason="$1"; usage; exit 2; }
[[ $# == 0 ]] || fail_input unexpected-arguments
case "$MODE" in fast|push|pr|full) ;; *) fail_input invalid-mode ;; esac
case "$MODE" in
  push|pr)
    [[ "$BASE_SHA" =~ ^[0-9a-fA-F]{40}$ && "$BASE_SHA" != 0000000000000000000000000000000000000000 ]] || fail_input invalid-base-sha
    ;;
  fast|full) [[ -z "$BASE_SHA" ]] || fail_input unexpected-base ;;
esac
if [[ "$MODE" != push && ( -n "${CI_PUSH_BEFORE:-}" || -n "${CI_PUSH_AFTER:-}" ) ]]; then
  fail_input unexpected-push-range
fi
# Native push changes both planning and every child's plan validation. This
# local door must never acquire an immutable CI event's different scope.
[[ "${GITHUB_EVENT_NAME:-}" != push ]] || fail_input inherited-push-event
ROOT="$(git rev-parse --show-toplevel)" || fail_input invalid-repository
cd "$ROOT"
CANDIDATE="$ROOT"
if [[ "$MODE" == fast ]]; then
  stage=fast
  make -C tools check-fast
  stage=complete
  exit 0
fi
# Reuse the shared parser for the only reusable-workflow identity input.
# Keep the accepted local environment intact throughout child validation.
python3 -B - "$ROOT" <<'PY' || fail_input inherited-workflow-inputs
import pathlib, sys
sys.path.insert(0, str(pathlib.Path(sys.argv[1]) / "tools/scripts/workflow"))
import ci_plan
try:
    if ci_plan.workflow_candidate() is not None:
        raise ValueError("local preflight does not accept reusable workflow candidate inputs")
except ValueError as error:
    print(str(error), file=sys.stderr)
    sys.exit(2)
PY
if [[ "$MODE" == push || "$MODE" == pr ]]; then
  [[ "$(git cat-file -t "$BASE_SHA" 2>/dev/null)" == commit ]] || fail_input unavailable-base-commit
  BASE_SHA="$(git rev-parse --verify "$BASE_SHA^{commit}")" || fail_input unavailable-base-commit
fi
HEAD_SHA="$(git rev-parse --verify 'HEAD^{commit}')" || fail_input uncommitted-head
[[ -z "${CANDIDATE_SHA:-}" || "$CANDIDATE_SHA" == "$HEAD_SHA" ]] || fail_input candidate-head-mismatch
export CANDIDATE_SHA="$HEAD_SHA"
if [[ "$MODE" == push && ( -n "${CI_PUSH_BEFORE:-}" || -n "${CI_PUSH_AFTER:-}" ) ]]; then
  [[ "${CI_PUSH_BEFORE:-}" == "$BASE_SHA" && "${CI_PUSH_AFTER:-}" == "$HEAD_SHA" ]] || fail_input conflicting-push-range
fi
if [[ "$MODE" == pr ]]; then
  status_output="$(git status --porcelain --untracked-files=all)" || fail_input status-observation-failed
  [[ -z "$status_output" ]] || fail_input dirty-tree
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
  git clone --quiet --shared --no-checkout --origin origin "$ROOT" "$CANDIDATE"
  # Bind the merged tree to its protected first parent and triggering head.
  CANDIDATE_SHA="$(git -C "$CANDIDATE" -c user.name=Preflight -c user.email=preflight@example.invalid \
    commit-tree "$TREE_SHA" -p "$BASE_SHA" -p "$HEAD_SHA" -m 'Preflight candidate')"
  git -C "$CANDIDATE" checkout --quiet --detach "$CANDIDATE_SHA"
  git -C "$CANDIDATE" remote remove origin
  stage=plan
  python3 -B "$CANDIDATE/tools/scripts/workflow/ci.py" pr-plan --repository "$CANDIDATE" \
    --commit "$CANDIDATE_SHA" --base "$BASE_SHA" --head "$HEAD_SHA"
  export CANDIDATE_SHA
  export CI_PLAN_PATH="$CANDIDATE/build/ci/plan.json"
  export CI_CHANGES_PATH="$CANDIDATE/build/ci/changes.json"
  printf 'PREFLIGHT_CANDIDATE path=%s\n' "$CANDIDATE"
else
  stage=plan
  range_options=()
  if [[ "$MODE" == push ]]; then range_options=(--before "$BASE_SHA" --after "$HEAD_SHA"); fi
  python3 -B tools/scripts/workflow/ci.py push-plan --repository "$ROOT" --commit "$HEAD_SHA" ${range_options[@]+"${range_options[@]}"}
  export CI_PLAN_PATH="$ROOT/build/ci/plan.json"
  export CI_CHANGES_PATH="$ROOT/build/ci/changes.json"
fi
if [[ -f "$ROOT/tools/scripts/lib/resource-observation-lib.sh" ]]; then
  source "$ROOT/tools/scripts/lib/resource-observation-lib.sh"
  resource_observe preflight-start "$CANDIDATE" || true
fi
cd "$CANDIDATE"
# Engineering normally owns the canonical build. A current-only plan needs the
# same producer before engineering records its honest not-required result.
build_without_engineering="$(python3 -B - "$CI_PLAN_PATH" <<'PY'
import json, sys
stages = json.load(open(sys.argv[1]))["stages"]
print("yes" if stages["build"]["status"] == "required" and stages["engineering"]["status"] == "not-required" else "no")
PY
)"
if [[ "$build_without_engineering" == yes ]]; then
  stage=build
  /bin/bash tools/scripts/ci-stage.sh "$stage"
fi
for stage in engineering current; do
  if [[ "$MODE" == pr && "$stage" == current ]]; then
    # The private clone has its own Git inventory. Only Lean's optional seed
    # lookup reads the source inventory; candidate code still owns all work.
    STRATALINT_LEAN_CACHE_DONOR_REPOSITORY="$ROOT" /bin/bash tools/scripts/ci-stage.sh "$stage"
  else
    /bin/bash tools/scripts/ci-stage.sh "$stage"
  fi
done
if [[ "$MODE" == pr ]]; then
  stage="delta"
  /bin/bash tools/scripts/ci-stage.sh delta "$BASE_SHA"
fi
stage=complete
