#!/usr/bin/env bash
set -euo pipefail
[[ $# == 0 || ( $# == 1 && ( "$1" == --batch || "$1" == --test ) ) ]] || {
  echo 'usage: auric-fib-analysis.sh [--batch] < request.json; or --test after build' >&2
  exit 2
}
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
[[ -f "$ROOT/.lake/.stratalint-lean-cache-stamp.json" ]] || {
  echo 'build first: make -C tools auric-fib-analysis-build' >&2; exit 2;
}
export GIT_OPTIONAL_LOCKS=0
cd "$ROOT"
if [[ ${1-} == --test ]]; then
  lake -d tools/lean-inspector-reg env lean --run tools/lean-inspector/LeanInformationAuditRegTests/AuricFib/RateBoundary.lean
  exec python3 -B "$ROOT/tools/lean-inspector/tests/test_auric_fib_analysis.py" "$ROOT/tools/scripts/auric-fib-analysis.sh"
fi
exec lake -d tools/lean-inspector-reg env lean --run tools/lean-inspector/LeanInformationAuditRegAnalysis/AuricFib/Main.lean "$@"
