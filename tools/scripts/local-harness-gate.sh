#!/bin/bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
CANDIDATE_ROOT="$ROOT"
BASE_REF=origin/dev
SKIP_ENGINEERING=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    --candidate) [[ $# -ge 2 ]] || exit 2; CANDIDATE_ROOT="$2"; shift 2 ;;
    --base) [[ $# -ge 2 ]] || exit 2; BASE_REF="$2"; shift 2 ;;
    --skip-engineering) [[ "$SKIP_ENGINEERING" == 0 ]] || exit 2; SKIP_ENGINEERING=1; shift ;;
    *) echo "local-harness-gate: unknown argument $1" >&2; exit 2 ;;
  esac
done
cd "$CANDIDATE_ROOT"
BASE_SHA="$(git rev-parse --verify "${BASE_REF}^{commit}")"
if [[ "$SKIP_ENGINEERING" == 0 ]]; then /bin/bash tools/scripts/ci-stage.sh engineering; fi
/bin/bash tools/scripts/ci-stage.sh current
/bin/bash tools/scripts/ci-stage.sh delta "$BASE_SHA"
