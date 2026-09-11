#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 || $# -gt 3 ]]; then
  echo "usage: scribe-content-checks.sh REPORT [SCRIBE_DLL [BASE]]" >&2
  exit 2
fi

REPORT="$1"
SCRIBE_DLL="${2:-}"
BASE="${3:-${STRATALINT_SCRIBE_BASE:-}}"
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
PROJECT="$REPO_ROOT/tools/StrataLint.Scribe.Documents/StrataLint.Scribe.Documents.csproj"
if [[ ! -s "$REPORT" ]]; then
  echo "scribe-content-checks: raw Lean report is missing or empty at $REPORT" >&2
  exit 2
fi
if [[ ! "$BASE" =~ ^[0-9a-fA-F]{40}$|^[0-9a-fA-F]{64}$ ]]; then
  echo "scribe-content-checks: an exact merge-base is required" >&2
  exit 2
fi
git -C "$REPO_ROOT" cat-file -e "${BASE}^{commit}" \
  || { echo "scribe-content-checks: BASE commit is unavailable" >&2; exit 2; }
SCRIBE=(dotnet run --project "$PROJECT" --configuration Release --)
if [[ -n "$SCRIBE_DLL" ]]; then
  SCRIBE=(dotnet "$SCRIBE_DLL")
fi

cd "$REPO_ROOT"
run_scribe() {
  STRATALINT_LEAN_REPORT="$REPORT" "${SCRIBE[@]}" "$@"
}

CHANGED_PATHS=()
while IFS= read -r -d '' path; do
  CHANGED_PATHS+=("$path")
done < <(
  git diff --name-only --no-renames -z "$BASE" --
  git ls-files --others --exclude-standard -z
)

# FILEMAP's registered manifest is the sole impact authority. Validate its
# inputs even on an unrelated delta; match removed paths from the same git diff.
selection="$(dotnet run --project "$REPO_ROOT/tools/StrataLint.Cli/StrataLint.Cli.csproj" \
  --configuration Release --no-launch-profile --disable-build-servers --verbosity quiet -- \
  filemap-conform --input-scopes scribe-projections,scribe-describe,scribe-markdown \
  --repository "$REPO_ROOT" --match-paths ${CHANGED_PATHS[@]+"${CHANGED_PATHS[@]}"})" \
  || { echo "scribe-content-checks: registered impact selection is unavailable" >&2; exit 2; }
checks="$(printf '%s' "$selection" | python3 -c '
import json, sys
selected = json.load(sys.stdin)
for scope in ("scribe-projections", "scribe-describe", "scribe-markdown"):
    if selected[scope]:
        print(scope)
')" || { echo "scribe-content-checks: registered impact selection is malformed" >&2; exit 2; }

requires_projection_check=0
requires_describe_check=0
requires_markdown_check=0
while IFS= read -r check; do
  case "$check" in
    scribe-projections) requires_projection_check=1 ;;
    scribe-describe) requires_describe_check=1 ;;
    scribe-markdown) requires_markdown_check=1 ;;
  esac
done <<< "$checks"

if [[ "$requires_projection_check" == "1" ]]; then
  run_scribe projections --check --report "$REPORT"
fi
if [[ "$requires_describe_check" == "1" ]]; then
  run_scribe describe-report --check
fi
# 判词只落在改动触及的那几篇文档上;路径经本块的标准输入交付,NUL 分隔,与 git 同口径,
# 因而不必落一个还要清理的临时文件。
if [[ "$requires_markdown_check" == "1" ]]; then
  run_scribe markdown-check --report "$REPORT" --paths-from -
fi < <(printf '%s\0' "${CHANGED_PATHS[@]}")
