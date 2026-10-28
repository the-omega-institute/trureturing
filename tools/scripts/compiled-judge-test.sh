#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
make -C "$ROOT" lean LEAN_TARGETS="regInspector/LeanInformationAuditRegTests regInspector/compiledJudgeTests leanInspector/reportInspector"
cd "$ROOT"
compute=()
[[ -z "${STRATALINT_CI_COMPUTE_BUDGET:-}" || "${STRATALINT_CI_COMPUTE_ACTIVE:-0}" == 1 ]] || compute=(python3 tools/scripts/workflow/ci_compute.py run --)
${compute[@]+"${compute[@]}"} lake -d tools/lean-inspector-reg env .lake/build/lean-inspector/reg/bin/compiledJudgeTests
