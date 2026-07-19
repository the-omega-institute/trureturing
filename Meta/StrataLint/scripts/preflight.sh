#!/bin/bash
# preflight: 提交前一键预证 CI 双 required check 会绿(本地=CI 同一器,器之四律②)
# 覆盖 engineering check 全步骤 + baseline admission(gate);CI=true 复现 CI 独有构建属性。
set -euo pipefail
ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"
source "$ROOT/Meta/StrataLint/scripts/perf-event-lib.sh"
PREFLIGHT_STARTED="$(date +%s)"
PERF_TMP="$(perf_make_spool_dir "$ROOT" stratalint-preflight-perf 2>/dev/null || true)"
PERF_EVENT_SPOOL=""
if [[ -n "$PERF_TMP" ]]; then
  PERF_EVENT_SPOOL="$PERF_TMP/events.jsonl"
  : > "$PERF_EVENT_SPOOL" || PERF_EVENT_SPOOL=""
fi
PERF_COMMIT="$(git rev-parse --verify HEAD 2>/dev/null || printf unknown)"
PERF_BASE="$(git rev-parse --verify "${BASE:-origin/dev}^{commit}" 2>/dev/null || printf unknown)"
STRATALINT_PERF_RUN_ID="${STRATALINT_PERF_RUN_ID:-preflight-${PREFLIGHT_STARTED}-$$-${PERF_COMMIT:0:12}}"
export STRATALINT_PERF_RUN_ID

finish_perf() {
  local rc=$?
  local status="failed"
  trap - EXIT
  set +e
  if [[ "$rc" -eq 0 ]]; then status="passed"; fi
  perf_capture_event \
    "$PERF_EVENT_SPOOL" "$ROOT" "$STRATALINT_PERF_RUN_ID" "preflight" "$PERF_BASE" \
    total "$status" "$(( $(date +%s) - PREFLIGHT_STARTED ))" || true
  perf_flush_events "$ROOT" "$PERF_EVENT_SPOOL" >/dev/null 2>&1 || true
  if [[ -n "$PERF_TMP" ]]; then rm -rf -- "$PERF_TMP"; fi
  exit "$rc"
}
trap finish_perf EXIT

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

dotnet restore Meta/StrataLint/CompileFailProof/CompileFailProof.csproj --locked-mode >/dev/null
dotnet restore Meta/StrataLint/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj --locked-mode >/dev/null
record_timing restore-proofs

CI=true make dotnet
record_timing dotnet

CI=true make test
record_timing test

make selftest
record_timing selftest

if dotnet build Meta/StrataLint/CompileFailProof/CompileFailProof.csproj --no-restore --configuration Release >/dev/null 2>&1; then
  echo "[preflight] FAIL: CompileFailProof 竟然编译通过(能力链证明失效)" >&2; exit 1
fi
if dotnet build Meta/StrataLint/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj --no-restore --configuration Release >/dev/null 2>&1; then
  echo "[preflight] FAIL: BannedApiCompileFailProof 竟然编译通过(禁 API 证明失效)" >&2; exit 1
fi
record_timing compile-fail-proofs

make gate BASE="${BASE:-origin/dev}" GATE_ARGS=--skip-engineering
record_timing gate

echo "[preflight] PASS — CI 双 required check 预证绿"
