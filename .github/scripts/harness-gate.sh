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

set +e
(
  cd "$CANDIDATE_ROOT"
  dotnet "$JUDGE_DLL" check --protected-base "$BASE_REF" \
    --candidate-lean-report "$CANDIDATE_LEAN_REPORT" \
    --baseline-lean-report "$BASELINE_LEAN_REPORT"
)
rc=$?
set -e
admission_status="passed"
if [[ "$rc" -ne 0 && "$rc" -ne 3 ]]; then admission_status="failed"; fi
mark admission "$admission_status"

# echo-verify runs the BASE judge binary, whose DocumentDefinitions.All is
# reflected from the base-compiled *.scribe.cs set. A protected-surface change
# (rc==3) that adds a new *.scribe.cs adds a definition the base binary cannot
# render, so echo-verify structurally always fails (out-of-date, N vs N+1) and,
# unguarded, killed the gate before verify-conservative — walling off ALL new D5
# theorem growth since 2026-07-22 (d5lean=0 regression, #406). rc==3 admission is
# already base-owned by verify-conservative (base-owned golden-corpus replay);
# the frozen-ledger validator, BACKFILL rule, conservativeness and SL-022 checks
# all remain. So restrict echo-verify to rc==0, where no protected file (hence no
# .scribe.cs) changed and the base binary can fully derive the residual.
# Accounted residual (第20条, low-harm/self-healing): a rc==3 PR editing an
# EXISTING .scribe.cs + faking Generated/echo-residual-summary.md (a
# non-authoritative photo of the admission-checked BACKFILL ledger) skips this
# base byte-check; it cannot corrupt the frozen ledger, and re-derives fresh on
# the next affected rc==0 PR. Surgical closure (base echo-verify -> NOT_APPLICABLE
# when the base cannot render, else enforce) is a deferred follow-up in #406.
if [[ $rc -eq 0 ]]; then
  (
    cd "$CANDIDATE_ROOT"
    STRATALINT_LEAN_REPORT="$CANDIDATE_LEAN_REPORT" \
      dotnet "$JUDGE_DLL" echo-verify \
        --base "$BASE_REF" --if-affected
  )
  mark echo-verify
fi

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
  conservative_status="passed"
  if [[ "$conservative_rc" -ne 0 ]]; then conservative_status="failed"; fi
  mark conservative "$conservative_status"
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
