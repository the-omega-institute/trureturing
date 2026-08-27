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
ENGINEERING_PLAN_FILE=""
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

finish_preflight() {
  local rc="$1"
  trap - EXIT
  trap '' INT TERM
  set +e
  if [[ -n "$ROOT" ]] && declare -F resource_observe >/dev/null; then
    resource_observe preflight-finish "$ROOT" || true
  fi
  if [[ -n "$ENGINEERING_PLAN_FILE" ]]; then rm -f -- "$ENGINEERING_PLAN_FILE"; fi
  exit "$rc"
}
trap 'finish_preflight "$?"' EXIT
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
source "$ROOT/tools/scripts/lib/resource-observation-lib.sh"

remote="${BASE_REF%%/*}"
if [[ "$remote" != "$BASE_REF" ]] && git remote | grep -Fxq "$remote"; then
  git fetch --prune "$remote"
fi
if ! admission_resolve_base "$ROOT" "$BASE_REF"; then
  exit 1
fi

PREFLIGHT_STARTED="$(date +%s)"
resource_observe preflight-start "$ROOT" || true

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

ENGINEERING_PLAN_FILE="$(mktemp "${TMPDIR:-/tmp}/stratalint-engineering-plan.XXXXXX")"
ENGINEERING_HEAD="$CANDIDATE_SHA"
ENGINEERING_BASE="$BASE_SHA"
CI=true STRATALINT_REQUIRE_LIVE_REPORT=1 make -C tools engineering-tests MODE=plan HEAD="$ENGINEERING_HEAD" BASE="$ENGINEERING_BASE" PLAN_FILE="$ENGINEERING_PLAN_FILE"
CI=true STRATALINT_REQUIRE_LIVE_REPORT=1 make -C tools engineering-tests MODE=execute HEAD="$ENGINEERING_HEAD" BASE="$ENGINEERING_BASE" PLAN_FILE="$ENGINEERING_PLAN_FILE"
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

prove_banned_api_compile_failure() {
  local project="tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj"
  local proof="tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs"
  local output=""
  local status=0
  set +e
  output="$(dotnet build "$project" --no-restore --configuration Release 2>&1)"
  status=$?
  set -e
  printf '%s\n' "$output"
  test "$status" -ne 0
  case "$status" in
    124|126|127|130|143) return "$status" ;;
  esac
  local expected_lines=()
  local actual_lines=()
  while IFS= read -r line; do expected_lines+=("$line"); done \
    < <(grep -nF "// banned-api-proof" "$proof" | cut -d: -f1)
  while IFS= read -r line; do actual_lines+=("$line"); done \
    < <(sed -n 's#.*BannedApiViolations.cs(\([0-9][0-9]*\),[0-9][0-9]*): error RS0030:.*#\1#p' <<<"$output" | sort -nu)
  test "${#expected_lines[@]}" -gt 0
  test "${#actual_lines[@]}" -eq "${#expected_lines[@]}"
  test -z "$(grep -F ': error ' <<<"$output" | grep -vF ': error RS0030:' || true)"
  local index=0
  for expected_line in "${expected_lines[@]}"; do
    test "${actual_lines[$index]}" = "$expected_line"
    ((index += 1))
  done
}

expect_compile_failure \
  tools/tests/CompileFailProof/CompileFailProof.csproj \
  CompileFailProof \
  "能力链证明失效"
prove_banned_api_compile_failure
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
