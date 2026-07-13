#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
CANDIDATE_ROOT="$ROOT"
BASE_REF="origin/dev"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --candidate) CANDIDATE_ROOT="$2"; shift 2 ;;
    --base) BASE_REF="$2"; shift 2 ;;
    *) echo "local-harness-gate: unknown arg '$1'" >&2; exit 2 ;;
  esac
done

[[ -d "$CANDIDATE_ROOT" ]] \
  || { echo "local-harness-gate: candidate '$CANDIDATE_ROOT' is absent" >&2; exit 2; }
CANDIDATE_ROOT="$(cd "$CANDIDATE_ROOT" && pwd -P)"
export PATH="$HOME/.elan/bin:/usr/local/share/dotnet:/opt/homebrew/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin:${PATH:-}"

remote="${BASE_REF%%/*}"
if [[ "$remote" != "$BASE_REF" ]] \
  && git -C "$CANDIDATE_ROOT" remote | grep -Fxq "$remote"; then
  git -C "$CANDIDATE_ROOT" fetch --prune "$remote"
fi
BASE_SHA="$(git -C "$CANDIDATE_ROOT" rev-parse --verify "${BASE_REF}^{commit}")"

TMP_ROOT="$(mktemp -d)"
JUDGE_ROOT=""
CREATED_JUDGE=0

cleanup() {
  if [[ "$CREATED_JUDGE" == "1" && -n "$JUDGE_ROOT" ]]; then
    git -C "$CANDIDATE_ROOT" worktree remove --force "$JUDGE_ROOT" >/dev/null 2>&1 || true
  fi
  rm -rf -- "$TMP_ROOT"
}
trap cleanup EXIT HUP INT TERM

current_path=""
current_head=""
current_branch=""
while IFS= read -r -d '' field; do
  case "$field" in
    worktree\ *) current_path="${field#worktree }" ;;
    HEAD\ *) current_head="${field#HEAD }" ;;
    branch\ *) current_branch="${field#branch }" ;;
    "")
      if [[ -z "$JUDGE_ROOT" \
        && "$current_head" == "$BASE_SHA" \
        && "$current_branch" == "refs/heads/dev" \
        && -d "$current_path" ]] \
        && git -C "$current_path" diff --quiet \
        && git -C "$current_path" diff --cached --quiet; then
        JUDGE_ROOT="$current_path"
      fi
      current_path=""
      current_head=""
      current_branch=""
      ;;
  esac
done < <(git -C "$CANDIDATE_ROOT" worktree list --porcelain -z)

if [[ -z "$JUDGE_ROOT" ]]; then
  JUDGE_ROOT="$TMP_ROOT/dev-judge"
  git -C "$CANDIDATE_ROOT" worktree add --detach "$JUDGE_ROOT" "$BASE_SHA"
  CREATED_JUDGE=1
fi

printf '[local-gate] candidate=%s judge=%s base=%s\n' \
  "$CANDIDATE_ROOT" "$JUDGE_ROOT" "$BASE_SHA" >&2

make -C "$CANDIDATE_ROOT" dotnet
make -C "$CANDIDATE_ROOT" test
make -C "$CANDIDATE_ROOT" selftest

LAKE_BIN="${LAKE_BIN:-$(command -v lake || true)}"
[[ -n "$LAKE_BIN" && "$LAKE_BIN" == /* && -x "$LAKE_BIN" ]] \
  || { echo "local-harness-gate: an absolute lake executable is required" >&2; exit 2; }
REPORTS="$TMP_ROOT/reports"
mkdir -p "$REPORTS"
PRODUCER="$JUDGE_ROOT/Meta/StrataLint/lean-inspector/inspect.sh"
[[ -x "$PRODUCER" ]] \
  || { echo "local-harness-gate: dev Lean producer is absent" >&2; exit 2; }

CANDIDATE_REPORT="$CANDIDATE_ROOT/.lake/build/stratalint/raw-lean-report.json"
LAKE_BIN="$LAKE_BIN" "$PRODUCER" \
  --repository "$CANDIDATE_ROOT" \
  --output "$CANDIDATE_REPORT"
LAKE_BIN="$LAKE_BIN" "$PRODUCER" \
  --repository "$JUDGE_ROOT" \
  --output "$REPORTS/baseline-lean-report.json"
SCRIBE_USE_EXISTING_REPORT=1 make -C "$CANDIDATE_ROOT" emit-check

GATE="$JUDGE_ROOT/.github/scripts/harness-gate.sh"
[[ -x "$GATE" ]] || { echo "local-harness-gate: dev gate is absent" >&2; exit 2; }
"$GATE" \
  --candidate "$CANDIDATE_ROOT" \
  --judge-root "$JUDGE_ROOT" \
  --base "$BASE_SHA" \
  --candidate-lean-report "$CANDIDATE_REPORT" \
  --baseline-lean-report "$REPORTS/baseline-lean-report.json"
