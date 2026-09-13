#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
BASE="${1:-origin/dev}"
REPORT_SCRIPT="$ROOT/tools/scripts/report/lean-report.sh"
PROJECT="$ROOT/tools/StrataLint.Cli/StrataLint.Cli.csproj"

cd "$ROOT"
BASE="$(git rev-parse --verify "${BASE}^{commit}")"
"$REPORT_SCRIPT" "$BASE" >&2
exec dotnet run --project "$PROJECT" --configuration Release -- \
  echo-verify --emit --base "$BASE"
