#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
make -C "$ROOT" lean LEAN_TARGETS="regInspector/LeanInformationAuditRegTests regInspector/compiledJudgeTests leanInspector/reportInspector regInspector/auricFibAnalysis"
cd "$ROOT"
lake -d tools/lean-inspector-reg env .lake/build/lean-inspector/reg/bin/compiledJudgeTests
python3 -B tools/lean-inspector/tests/test_auric_fib_universal.py -v
/bin/bash tools/scripts/auric-fib-analysis.sh --test
