#!/bin/bash
# preflight: 一键预证 CI 三 required check 会绿(本地=CI 同一器,器律②)。
# 提交前不强制跑本器(用户 2026-08-26 定,见 CLAUDE.md 器律②);CI 红了用它定位。
# 覆盖 engineering 全步骤、lean-inspect 的数学内容检查与 baseline admission(gate);
# CI=true 复现 CI 独有构建属性。
set -euo pipefail

ROOT=""
PREFLIGHT_STARTED=0
BASE_REF="${BASE:-origin/dev}"
BASE_TIP_SHA=""
BASE_SHA=""
CANDIDATE_SHA=""
PREFLIGHT_DEADLINE_AT="${PREFLIGHT_DEADLINE_AT:-}"

# Remaining seconds of preflight's optional absolute deadline, or empty when unbounded.
remaining_deadline_seconds() {
  local deadline="$PREFLIGHT_DEADLINE_AT"
  [[ "$deadline" =~ ^[0-9]+$ ]] || return 1
  local now
  now="$(date +%s)"
  [[ "$now" =~ ^[0-9]+$ ]] || return 1
  printf '%s\n' "$(( deadline - now ))"
}

trap 'exit 130' INT
trap 'exit 143' TERM

for tool in git make dotnet lake; do
  command -v "$tool" >/dev/null 2>&1 || exit 127
done
dotnet --version >/dev/null
lake --version >/dev/null

ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"
source "$ROOT/tools/scripts/lib/admission-base-lib.sh"

remote="${BASE_REF%%/*}"
if [[ "$remote" != "$BASE_REF" ]] && git remote | grep -Fxq "$remote"; then
  git fetch --prune "$remote"
fi
if ! admission_resolve_base "$ROOT" "$BASE_REF"; then
  exit 1
fi

PREFLIGHT_STARTED="$(date +%s)"

record_timing() {
  local stage="$1"
  local elapsed="$(( $(date +%s) - T ))"
  printf '[preflight] %-22s %ss\n' "$stage" "$elapsed"
  T=$(date +%s)
}
T=$(date +%s)

dotnet restore tools/tests/CompileFailProof/CompileFailProof.csproj --locked-mode >/dev/null
dotnet restore tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj --locked-mode >/dev/null
record_timing restore-proofs

CI=true make -C tools dotnet
record_timing dotnet

make lean-report
record_timing lean-report

STRATALINT_SCRIBE_BASE="$BASE_SHA" \
  /bin/bash "$ROOT/tools/scripts/workflow/scribe-content-checks.sh" \
  "$ROOT/.lake/build/stratalint/raw-lean-report.json"
record_timing scribe-content-checks

CI=true STRATALINT_REQUIRE_LIVE_REPORT=1 make -C tools test
record_timing test

make -C tools selftest
record_timing selftest

expect_compile_failure() {
  local project="$1"
  local label="$2"
  local failure_reason="$3"
  local rc=0
  set +e
  dotnet build "$project" --no-restore --configuration Release >/dev/null 2>&1
  rc=$?
  set -e
  if [[ "$rc" -eq 0 ]]; then
    echo "[preflight] FAIL: $label 竟然编译通过($failure_reason)" >&2
    return 1
  fi
  case "$rc" in
    124|126|127|130|143) return "$rc" ;;
  esac
  return 0
}

expect_compile_failure \
  tools/tests/CompileFailProof/CompileFailProof.csproj \
  CompileFailProof \
  "能力链证明失效"
expect_compile_failure \
  tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj \
  BannedApiCompileFailProof \
  "禁 API 证明失效"
record_timing compile-fail-proofs

# Measure what is left of the outer deadline before entering the most expensive stage,
# and name the owner when it is already spent. Without this the gate starts, runs its
# own report production against an inner budget, and the eventual timeout is reported as
# whatever inner step happened to be running -- pointing at the symptom rather than at
# the budget that actually ran out.
if gate_remaining="$(remaining_deadline_seconds)"; then
  if [[ "$gate_remaining" -le 0 ]]; then
    printf 'PREFLIGHT_BUDGET_EXHAUSTED owner=outer-deadline stage=gate remaining_seconds=%s deadline_at=%s\n' \
      "$gate_remaining" "$PREFLIGHT_DEADLINE_AT" >&2
    exit 124
  fi
  printf 'PREFLIGHT_BUDGET owner=outer-deadline stage=gate remaining_seconds=%s\n' "$gate_remaining"
fi

set +e
make gate BASE="$BASE_SHA" GATE_ARGS="--skip-engineering"
gate_rc=$?
set -e
record_timing gate

observed_base="$(git rev-parse --verify "${BASE_REF}^{commit}" 2>/dev/null || true)"
if [[ -n "$observed_base" && "$observed_base" != "$BASE_TIP_SHA" ]]; then
  printf 'BASE_ADVANCED pinned=%s observed=%s\n' "$BASE_TIP_SHA" "$observed_base" || true
fi
if [[ "$gate_rc" -ne 0 ]]; then exit "$gate_rc"; fi

echo "[preflight] PASS — CI 三 required check 预证绿"
