#!/usr/bin/env bash
# Shared .NET admission gate. Lean inspection is a predecessor data-producing
# stage; this program consumes its two canonical reports and never invokes Lean.
set -euo pipefail

CANDIDATE_ROOT="."
JUDGE_ROOT=""
BASE_REF=""
CANDIDATE_LEAN_REPORT=""
BASELINE_LEAN_REPORT=""
LEGACY_BOOTSTRAP=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --candidate) CANDIDATE_ROOT="$2"; shift 2 ;;
    --judge-root) JUDGE_ROOT="$2"; shift 2 ;;
    --base) BASE_REF="$2"; shift 2 ;;
    --candidate-lean-report) CANDIDATE_LEAN_REPORT="$2"; shift 2 ;;
    --baseline-lean-report) BASELINE_LEAN_REPORT="$2"; shift 2 ;;
    --legacy-bootstrap) LEGACY_BOOTSTRAP=1; shift ;;
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
DLL_REL="Meta/StrataLint/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll"

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

selftest_dir="$(mktemp -d)"
(
  cd "$JUDGE_ROOT"
  dotnet "$DLL_REL" selftest > "$selftest_dir/a"
  dotnet "$DLL_REL" selftest > "$selftest_dir/b"
)
cmp "$selftest_dir/a" "$selftest_dir/b"
mark selftest

export STRATALINT_TIMING="${STRATALINT_TIMING:-1}"
set +e
if [[ "$LEGACY_BOOTSTRAP" == "1" ]]; then
  (
    cd "$CANDIDATE_ROOT"
    dotnet "$JUDGE_ROOT/$DLL_REL" check --protected-base "$BASE_REF"
  )
else
  (
    cd "$CANDIDATE_ROOT"
    dotnet "$JUDGE_ROOT/$DLL_REL" check --protected-base "$BASE_REF" \
      --candidate-lean-report "$CANDIDATE_LEAN_REPORT" \
      --baseline-lean-report "$BASELINE_LEAN_REPORT"
  )
fi
rc=$?
set -e
mark admission

if [[ "$LEGACY_BOOTSTRAP" == "1" ]]; then
  if [[ $rc -ne 3 ]]; then
    echo "harness-gate: legacy baseline judge must return SL-022 exit 3, got $rc" >&2
    exit 2
  fi

  summary "### SL-022 report-consumer bootstrap observed by predecessor judge"
  exit 0
fi

if [[ $rc -eq 0 ]]; then
  summary "### Admission: content fully validated, no protected-surface change"
  exit 0
fi

if [[ $rc -eq 3 ]]; then
  echo "::warning title=SL-022 protected-surface change::Bootstrap scaffold path; the predecessor Lean inspection stage supplied the kernel build floor." 2>/dev/null || true
  summary "### SL-022 protected-surface change (bootstrap scaffold path)"
  exit 0
fi

exit "$rc"
