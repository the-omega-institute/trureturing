#!/bin/bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
CANDIDATE_ROOT="$ROOT"
BASE_REF=origin/dev
while [[ $# -gt 0 ]]; do
  case "$1" in
    --candidate) [[ $# -ge 2 ]] || exit 2; CANDIDATE_ROOT="$2"; shift 2 ;;
    --base) [[ $# -ge 2 ]] || exit 2; BASE_REF="$2"; shift 2 ;;
    *) echo "local-harness-gate: unknown argument $1" >&2; exit 2 ;;
  esac
done
cd "$CANDIDATE_ROOT"
BASE_SHA="$(git rev-parse --verify "${BASE_REF}^{commit}")"
make lean-report
dotnet build tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -nologo
CLI=tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll
dotnet "$CLI" check-current --candidate-lean-report .lake/build/stratalint/raw-lean-report.json
bash tools/scripts/workflow/scribe-content-checks.sh .lake/build/stratalint/raw-lean-report.json
dotnet "$CLI" filemap-conform
dotnet "$CLI" check-delta --protected-base "$BASE_SHA" --candidate-lean-report .lake/build/stratalint/raw-lean-report.json
