#!/usr/bin/env bash
# Default dev ci.yml transition. Remove after successful ci-push/ci-pr checks
# and required-set migration; the final workflows use the common stages directly.
set -euo pipefail

CANDIDATE_ROOT="."
BASE=""
REPORT=""
JUDGE_HINT=""
while [[ $# -gt 0 ]]; do
  [[ $# -ge 2 && -n "$2" ]] || { echo "harness-gate: options require values" >&2; exit 2; }
  case "$1" in
    --candidate) CANDIDATE_ROOT="$2" ;;
    --base) BASE="$2" ;;
    --candidate-lean-report) REPORT="$2" ;;
    --judge-dll) JUDGE_HINT="$2" ;;
    *) echo "harness-gate: unknown argument '$1'" >&2; exit 2 ;;
  esac
  shift 2
done
[[ "$BASE" =~ ^[0-9a-f]{40}$ && -f "$REPORT" ]] \
  || { echo "harness-gate: immutable --base and --candidate-lean-report file are required" >&2; exit 2; }
CANDIDATE_ROOT="$(cd "$CANDIDATE_ROOT" && pwd -P)"
REPORT="$(cd "$(dirname "$REPORT")" && pwd -P)/$(basename "$REPORT")"
args=(--protected-base "$BASE" --candidate-lean-report "$REPORT")

# The old caller may supply a cached runtime hint. The canonical build supplies
# candidate binaries, with no separate judge builder.
if [[ -n "$JUDGE_HINT" ]]; then
  echo "harness-gate: cached judge hint superseded by the canonical candidate build" >&2
fi
make -C "$CANDIDATE_ROOT/tools" dotnet
cd "$CANDIDATE_ROOT"
judge="$CANDIDATE_ROOT/tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll"
check_exit=0
dotnet "$judge" check "${args[@]}" || check_exit=$?
filemap_exit=0
dotnet "$judge" filemap-conform || filemap_exit=$?
if [[ "$check_exit" -ne 0 && "$check_exit" -ne 3 ]]; then exit "$check_exit"; fi
if [[ "$filemap_exit" -ne 0 ]]; then exit "$filemap_exit"; fi
exit "$check_exit"
