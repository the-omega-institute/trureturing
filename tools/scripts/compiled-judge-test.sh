#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
# Lake schedules library modules concurrently. Search-reduction fixtures execute
# isolated compiler probes and are the high-memory part of this library, so
# compile those modules one at a time before the ordinary aggregate build.
make -C "$ROOT" search-reduction-index-fixtures
search_reduction_modules=(
  GraphCandidates GraphModel LookupModel LookupBaseline LookupTests LookupRecallTests LookupColdTests LookupCacheTests LookupIsolationTests GraphCalibration Baseline Model FiniteModel PresentationBaseline Candidates PresentationCandidates
  FaultPaths SingleSourceModel PresentationCoverage RawOriginsTests SingleSourceTests
  Calibration Faults RealNegative
  VocabularyCandidates VocabularyModel VocabularyTransport VocabularyTests InformationTests
)
for module in "${search_reduction_modules[@]}"; do
  make -C "$ROOT" lean \
    LEAN_TARGETS="LeanInformationAuditRegTests.SearchReduction.$module"
done
make -C "$ROOT" lean LEAN_TARGETS="regInspector/LeanInformationAuditRegTests regInspector/compiledJudgeTests leanInspector/reportInspector"
cd "$ROOT"
compute=()
[[ -z "${STRATALINT_CI_COMPUTE_BUDGET:-}" || "${STRATALINT_CI_COMPUTE_ACTIVE:-0}" == 1 ]] || compute=(python3 tools/scripts/workflow/ci_compute.py run --)
${compute[@]+"${compute[@]}"} lake -d tools/lean-inspector-reg env .lake/build/lean-inspector/reg/bin/compiledJudgeTests
