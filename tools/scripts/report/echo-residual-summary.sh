#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
BASE="${1:-origin/dev}"
REPORT_SCRIPT="$ROOT/tools/scripts/report/lean-report.sh"
PROJECT="$ROOT/tools/StrataLint.Cli/StrataLint.Cli.csproj"

BASE="$(git -C "$ROOT" rev-parse --verify "${BASE}^{commit}")"
"$REPORT_SCRIPT" --protected-base "$BASE" >&2
cd "$ROOT"
exec dotnet run --project "$PROJECT" --configuration Release -- \
  echo-verify --emit --base "$BASE"
