#!/bin/bash
# preflight: 提交前一键预证 CI 双 required check 会绿(本地=CI 同一器,器之四律②)
# 覆盖 engineering check 全步骤 + baseline admission(gate);CI=true 复现 CI 独有构建属性。
set -euo pipefail

ROOT=""
PREFLIGHT_STARTED=0
PREFLIGHT_FAULT_CLASS="CONFIGURATION"
PERF_TMP=""
PERF_EVENT_SPOOL=""
PERF_BASE="unknown"
BASE_REF="${BASE:-origin/dev}"
BASE_SHA=""
STRATALINT_PERF_RUN_ID=""

finish_preflight() {
  local rc="$1"
  local declaration="UNKNOWN:UNKNOWN"
  local status="failed"
  local finished_at="$PREFLIGHT_STARTED"
  trap - EXIT
  trap '' INT TERM
  set +e
  set +u

  if [[ "$rc" -eq 0 ]]; then
    declaration="PASS:NONE"
    status="passed"
  else
    case "$rc" in
      124|130|143) declaration="FAIL:INFRASTRUCTURE" ;;
      126|127) declaration="FAIL:TOOLCHAIN" ;;
      *)
        case "$PREFLIGHT_FAULT_CLASS" in
          SEMANTIC|CONFIGURATION|TOOLCHAIN|INFRASTRUCTURE)
            declaration="FAIL:$PREFLIGHT_FAULT_CLASS"
            ;;
        esac
        ;;
    esac
  fi

  finished_at="$(date +%s 2>/dev/null || printf '%s' "$PREFLIGHT_STARTED")"
  if [[ -n "$ROOT" ]] && declare -F perf_capture_event >/dev/null; then
    perf_capture_event \
      "$PERF_EVENT_SPOOL" "$ROOT" "$STRATALINT_PERF_RUN_ID" "preflight" "$PERF_BASE" \
      total "$status" "$(( finished_at - PREFLIGHT_STARTED ))" || true
    perf_flush_events "$ROOT" "$PERF_EVENT_SPOOL" >/dev/null 2>&1 || true
  fi
  if [[ -n "$PERF_TMP" ]]; then rm -rf -- "$PERF_TMP"; fi
  printf 'FKST_LOCAL_ITERATION_RESULT:v2:%s\n' "$declaration"
  exit "$rc"
}
trap 'finish_preflight "$?"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

PREFLIGHT_FAULT_CLASS="TOOLCHAIN"
for tool in git make dotnet lake; do
  command -v "$tool" >/dev/null 2>&1 || exit 127
done
dotnet --version >/dev/null
lake --version >/dev/null

PREFLIGHT_FAULT_CLASS="CONFIGURATION"
ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"

remote="${BASE_REF%%/*}"
if [[ "$remote" != "$BASE_REF" ]] && git remote | grep -Fxq "$remote"; then
  git fetch --prune "$remote"
fi
BASE_SHA="$(git rev-parse --verify "${BASE_REF}^{commit}")"
CANDIDATE_SHA="$(git rev-parse --verify HEAD^{commit})"
if [[ "$BASE_SHA" == "$CANDIDATE_SHA" ]] \
  || ! git merge-base --is-ancestor "$BASE_SHA" "$CANDIDATE_SHA"; then
  echo "preflight: pinned base is not a strict ancestor of candidate HEAD" >&2
  exit 1
fi

source "$ROOT/Meta/StrataLint/scripts/perf-event-lib.sh"
PREFLIGHT_STARTED="$(date +%s)"
PERF_TMP="$(perf_make_spool_dir "$ROOT" stratalint-preflight-perf 2>/dev/null || true)"
if [[ -n "$PERF_TMP" ]]; then
  PERF_EVENT_SPOOL="$PERF_TMP/events.jsonl"
  : > "$PERF_EVENT_SPOOL" || PERF_EVENT_SPOOL=""
fi
PERF_COMMIT="$(git rev-parse --verify HEAD 2>/dev/null || printf unknown)"
PERF_BASE="$BASE_SHA"
STRATALINT_PERF_RUN_ID="${STRATALINT_PERF_RUN_ID:-preflight-${PREFLIGHT_STARTED}-$$-${PERF_COMMIT:0:12}}"
export STRATALINT_PERF_RUN_ID

record_timing() {
  local stage="$1"
  local elapsed="$(( $(date +%s) - T ))"
  printf '[preflight] %-22s %ss\n' "$stage" "$elapsed"
  perf_capture_event \
    "$PERF_EVENT_SPOOL" "$ROOT" "$STRATALINT_PERF_RUN_ID" "preflight" "$PERF_BASE" \
    "$stage" passed "$elapsed" || true
  T=$(date +%s)
}
T=$(date +%s)

PREFLIGHT_FAULT_CLASS="UNKNOWN"
dotnet restore Meta/StrataLint/CompileFailProof/CompileFailProof.csproj --locked-mode >/dev/null
dotnet restore Meta/StrataLint/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj --locked-mode >/dev/null
record_timing restore-proofs

PREFLIGHT_FAULT_CLASS="UNKNOWN"
CI=true make dotnet
record_timing dotnet

PREFLIGHT_FAULT_CLASS="UNKNOWN"
make lean-report
record_timing lean-report

PREFLIGHT_FAULT_CLASS="SEMANTIC"
CI=true make test
record_timing test

PREFLIGHT_FAULT_CLASS="SEMANTIC"
make lua-test
record_timing lua-test

PREFLIGHT_FAULT_CLASS="SEMANTIC"
make selftest
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

PREFLIGHT_FAULT_CLASS="SEMANTIC"
expect_compile_failure \
  Meta/StrataLint/CompileFailProof/CompileFailProof.csproj \
  CompileFailProof \
  "能力链证明失效"
expect_compile_failure \
  Meta/StrataLint/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj \
  BannedApiCompileFailProof \
  "禁 API 证明失效"
record_timing compile-fail-proofs

PREFLIGHT_FAULT_CLASS="SEMANTIC"
set +e
make gate BASE="$BASE_SHA" GATE_ARGS=--skip-engineering
gate_rc=$?
set -e
record_timing gate

observed_base="$(git rev-parse --verify "${BASE_REF}^{commit}" 2>/dev/null || true)"
if [[ -n "$observed_base" && "$observed_base" != "$BASE_SHA" ]]; then
  printf 'BASE_ADVANCED pinned=%s observed=%s\n' "$BASE_SHA" "$observed_base" || true
fi
if [[ "$gate_rc" -ne 0 ]]; then exit "$gate_rc"; fi

echo "[preflight] PASS — CI 双 required check 预证绿"
