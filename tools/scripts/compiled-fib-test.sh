#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
make -C "$ROOT" lean LEAN_TARGETS="regInspector/LeanInformationAuditFibTests regInspector/compiledFibTests regInspector/auricFibAnalysis leanInspector/reportInspector"
cd "$ROOT"
compute=()
[[ -z "${STRATALINT_CI_COMPUTE_BUDGET:-}" || "${STRATALINT_CI_COMPUTE_ACTIVE:-0}" == 1 ]] || compute=(python3 tools/scripts/workflow/ci_compute.py run --)
${compute[@]+"${compute[@]}"} lake -d tools/lean-inspector-reg env .lake/build/lean-inspector/reg/bin/compiledFibTests
${compute[@]+"${compute[@]}"} python3 -B tools/lean-inspector/tests/test_auric_fib_universal.py -v
${compute[@]+"${compute[@]}"} /bin/bash tools/scripts/auric-fib-analysis.sh --test
