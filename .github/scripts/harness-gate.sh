#!/usr/bin/env bash
# Shared .NET admission gate. Lean inspection is a predecessor data-producing
# stage; this program consumes its two canonical reports and never invokes Lean.
set -euo pipefail

CANDIDATE_ROOT="."
JUDGE_ROOT=""
BASE_REF=""
CANDIDATE_LEAN_REPORT=""
BASELINE_LEAN_REPORT=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --candidate) CANDIDATE_ROOT="$2"; shift 2 ;;
    --judge-root) JUDGE_ROOT="$2"; shift 2 ;;
    --base) BASE_REF="$2"; shift 2 ;;
    --candidate-lean-report) CANDIDATE_LEAN_REPORT="$2"; shift 2 ;;
    --baseline-lean-report) BASELINE_LEAN_REPORT="$2"; shift 2 ;;
    *) echo "harness-gate: unknown arg '$1'" >&2; exit 2 ;;
  esac
done

[[ -n "$BASE_REF" ]] || { echo "harness-gate: --base REV is required" >&2; exit 2; }
[[ -n "$CANDIDATE_LEAN_REPORT" ]] \
  || { echo "harness-gate: --candidate-lean-report FILE is required" >&2; exit 2; }
[[ -n "$BASELINE_LEAN_REPORT" ]] \
  || { echo "harness-gate: --baseline-lean-report FILE is required" >&2; exit 2; }
[[ -d "$CANDIDATE_ROOT" ]] \
  || { echo "harness-gate: candidate root '$CANDIDATE_ROOT' is absent" >&2; exit 2; }
[[ -n "$JUDGE_ROOT" ]] || JUDGE_ROOT="$CANDIDATE_ROOT"
[[ -d "$JUDGE_ROOT" ]] \
  || { echo "harness-gate: judge root '$JUDGE_ROOT' is absent" >&2; exit 2; }
[[ -f "$CANDIDATE_LEAN_REPORT" ]] \
  || { echo "harness-gate: candidate Lean report '$CANDIDATE_LEAN_REPORT' is absent" >&2; exit 2; }
[[ -f "$BASELINE_LEAN_REPORT" ]] \
  || { echo "harness-gate: baseline Lean report '$BASELINE_LEAN_REPORT' is absent" >&2; exit 2; }

CANDIDATE_ROOT="$(cd "$CANDIDATE_ROOT" && pwd -P)"
JUDGE_ROOT="$(cd "$JUDGE_ROOT" && pwd -P)"
CANDIDATE_LEAN_REPORT="$(cd "$(dirname "$CANDIDATE_LEAN_REPORT")" && pwd -P)/$(basename "$CANDIDATE_LEAN_REPORT")"
BASELINE_LEAN_REPORT="$(cd "$(dirname "$BASELINE_LEAN_REPORT")" && pwd -P)/$(basename "$BASELINE_LEAN_REPORT")"
CLI_PROJECT_REL="Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj"

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

_t0=$(date +%s)
mark() {
  local now
  now=$(date +%s)
  printf '[gate] %-16s %ss\n' "$1" "$((now-_t0))" >&2
  _t0=$now
}

dotnet restore "$JUDGE_ROOT/Meta/StrataLint/StrataLint.sln" --locked-mode
dotnet build \
  "$JUDGE_ROOT/Meta/StrataLint/StrataLint.sln" \
  --no-restore \
  --configuration Release \
  --warnaserror
mark build-judge
JUDGE_DLL="$(resolve_target_path "$JUDGE_ROOT")"

selftest_dir="$(mktemp -d)"
(
  cd "$JUDGE_ROOT"
  dotnet "$JUDGE_DLL" selftest > "$selftest_dir/a"
  dotnet "$JUDGE_DLL" selftest > "$selftest_dir/b"
)
cmp "$selftest_dir/a" "$selftest_dir/b"
mark selftest

export STRATALINT_TIMING="${STRATALINT_TIMING:-1}"
set +e
(
  cd "$CANDIDATE_ROOT"
  dotnet "$JUDGE_DLL" check --protected-base "$BASE_REF" \
    --candidate-lean-report "$CANDIDATE_LEAN_REPORT" \
    --baseline-lean-report "$BASELINE_LEAN_REPORT"
)
rc=$?
set -e
mark admission

if [[ $rc -eq 0 ]]; then
  summary "### Admission: content fully validated, no protected-surface change"
  exit 0
fi

if [[ $rc -eq 3 ]]; then
  make -C "$CANDIDATE_ROOT" dotnet
  mark build-candidate
  CANDIDATE_DLL="$(resolve_target_path "$CANDIDATE_ROOT")"
  set +e
  (
    cd "$JUDGE_ROOT"
    dotnet "$JUDGE_DLL" verify-conservative \
      --baseline-root "$JUDGE_ROOT" \
      --candidate-root "$CANDIDATE_ROOT" \
      --baseline-lean-report "$BASELINE_LEAN_REPORT" \
      --candidate-lean-report "$CANDIDATE_LEAN_REPORT" \
      --baseline-harness "$JUDGE_DLL" \
      --candidate-harness "$CANDIDATE_DLL"
  )
  conservative_rc=$?
  set -e
  mark conservative
  case "$conservative_rc" in
    0)
      summary "### SL-022 protected-surface change: conservative-extension certificate emitted"
      exit 3
      ;;
    1)
      summary "### SL-022 protected-surface change: conservative-extension violation"
      exit 1
      ;;
    2)
      summary "### SL-022 protected-surface change: conservative-extension infrastructure failure"
      exit 2
      ;;
    *)
      echo "harness-gate: verify-conservative returned invalid rc=$conservative_rc" >&2
      exit 2
      ;;
  esac
fi

exit "$rc"
