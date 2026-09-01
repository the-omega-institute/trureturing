#!/usr/bin/env bash
# Shared .NET admission gate. Lean inspection is a predecessor data-producing
# stage; this program consumes the candidate canonical report and never invokes Lean.
set -euo pipefail

CANDIDATE_ROOT="."
BASE_REF=""
CANDIDATE_LEAN_REPORT=""
JUDGE_DLL=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --candidate) CANDIDATE_ROOT="$2"; shift 2 ;;
    --base) BASE_REF="$2"; shift 2 ;;
    --candidate-lean-report) CANDIDATE_LEAN_REPORT="$2"; shift 2 ;;
    --judge-dll) JUDGE_DLL="$2"; shift 2 ;;
    *) echo "harness-gate: unknown arg '$1'" >&2; exit 2 ;;
  esac
done

[[ -n "$BASE_REF" ]] || { echo "harness-gate: --base REV is required" >&2; exit 2; }
[[ -n "$CANDIDATE_LEAN_REPORT" ]] \
  || { echo "harness-gate: --candidate-lean-report FILE is required" >&2; exit 2; }
[[ -d "$CANDIDATE_ROOT" ]] \
  || { echo "harness-gate: candidate root '$CANDIDATE_ROOT' is absent" >&2; exit 2; }
[[ -f "$CANDIDATE_LEAN_REPORT" ]] \
  || { echo "harness-gate: candidate Lean report '$CANDIDATE_LEAN_REPORT' is absent" >&2; exit 2; }

CANDIDATE_ROOT="$(cd "$CANDIDATE_ROOT" && pwd -P)"
CANDIDATE_LEAN_REPORT="$(cd "$(dirname "$CANDIDATE_LEAN_REPORT")" && pwd -P)/$(basename "$CANDIDATE_LEAN_REPORT")"
if [[ -n "$JUDGE_DLL" ]]; then
  [[ -f "$JUDGE_DLL" ]] \
    || { echo "harness-gate: external judge DLL '$JUDGE_DLL' is absent" >&2; exit 2; }
  JUDGE_DLL="$(cd "$(dirname "$JUDGE_DLL")" && pwd -P)/$(basename "$JUDGE_DLL")"
fi
CLI_PROJECT_REL="tools/StrataLint.Cli/StrataLint.Cli.csproj"

resolve_target_path() {
  local root="$1"
  local target
  target="$(dotnet msbuild "$root/$CLI_PROJECT_REL" \
    -getProperty:TargetPath \
    -property:Configuration=Release \
    -verbosity:quiet)"
  [[ -n "$target" && "$target" == /* && "$target" != *$'\n'* ]] \
    || { echo "harness-gate: MSBuild returned an invalid TargetPath for '$root'" >&2; return 2; }
  [[ "$target" == "$root/"* ]] \
    || { echo "harness-gate: TargetPath escapes repository '$root': $target" >&2; return 2; }
  [[ -f "$target" ]] \
    || { echo "harness-gate: TargetPath is absent: $target" >&2; return 2; }
  printf '%s\n' "$target"
}

summary() {
  if [[ -n "${GITHUB_STEP_SUMMARY:-}" ]]; then
    printf '%s\n' "$1" >> "$GITHUB_STEP_SUMMARY"
  else
    printf '%s\n' "$1"
  fi
}

if [[ -n "${STRATALINT_TIMING:-}" && "$STRATALINT_TIMING" != /* ]]; then
  echo "harness-gate: STRATALINT_TIMING must be an absolute JSONL path" >&2
  exit 2
fi

_t0=$(date +%s)
mark() {
  local stage="$1"
  local status="${2:-passed}"
  local now
  now=$(date +%s)
  printf '[gate] %-16s %ss\n' "$stage" "$((now-_t0))" >&2
  if [[ -n "${STRATALINT_TIMING:-}" ]]; then
    printf '{"event":"gate_stage_timing","scope":"admission","stage":"%s","status":"%s","elapsed_seconds":%s}\n' \
      "$stage" "$status" "$((now-_t0))" >> "$STRATALINT_TIMING"
  fi
  _t0=$now
}

# The judge ANALYSES the candidate tree with Roslyn symbol binding, so the solution's
# compile assets must be present whether or not the judge binary itself was built here.
# Restoring only on the cache-miss path made ScribeTestMapDeriver fail to bind xUnit
# symbols on cache hits, inflating the conservative unknown count from <=281 to 673 and
# blocking correct pull requests (issue #4513).
dotnet restore "$CANDIDATE_ROOT/tools/StrataLint.sln" --locked-mode
mark restore-solution

if [[ -z "$JUDGE_DLL" ]]; then
  dotnet build \
    "$CANDIDATE_ROOT/tools/StrataLint.sln" \
    --no-restore \
    --configuration Release \
    --warnaserror
  mark build-judge
  JUDGE_DLL="$(resolve_target_path "$CANDIDATE_ROOT")"
else
  mark cached-judge
fi

set +e
(
  cd "$CANDIDATE_ROOT"
  dotnet "$JUDGE_DLL" check --protected-base "$BASE_REF" \
    --candidate-lean-report "$CANDIDATE_LEAN_REPORT"
)
rc=$?
set -e
admission_status="passed"
if [[ "$rc" -ne 0 && "$rc" -ne 3 ]]; then admission_status="failed"; fi
mark admission "$admission_status"

set +e
(
  cd "$CANDIDATE_ROOT"
  dotnet "$JUDGE_DLL" filemap-conform
)
conform_rc=$?
set -e
conform_status="passed"
if [[ "$conform_rc" -ne 0 ]]; then conform_status="failed"; fi
mark filemap-conform "$conform_status"

case "$rc" in
  1) exit 1 ;;
  2) exit 2 ;;
esac

case "$conform_rc" in
  0) ;;
  1) exit 1 ;;
  2) exit 2 ;;
  *) exit "$conform_rc" ;;
esac

if [[ $rc -eq 0 ]]; then
  summary "### Admission: content fully validated, no protected-surface change"
  exit 0
fi

if [[ $rc -eq 3 ]]; then
  summary "protected-surface change (SL-022); content checks passed"
  exit 3
fi

exit "$rc"
