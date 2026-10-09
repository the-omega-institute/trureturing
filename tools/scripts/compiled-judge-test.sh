#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
make -C "$ROOT" lean LEAN_TARGETS="regInspector/LeanInformationAuditRegTests regInspector/compiledJudgeTests leanInspector/reportInspector"
cd "$ROOT"
lake -d tools/lean-inspector-reg env .lake/build/lean-inspector/reg/bin/compiledJudgeTests
make -C tools auric-fib-analysis-test
