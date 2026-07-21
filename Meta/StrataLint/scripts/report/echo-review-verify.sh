#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd -P)"
BASE="${1:-origin/dev}"
ECHO_REVIEW="${2:-.echo-review.md}"
REPORT_SCRIPT="$ROOT/Meta/StrataLint/scripts/report/lean-report.sh"
PROJECT="$ROOT/Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj"

"$REPORT_SCRIPT" >&2
cd "$ROOT"
exec dotnet run --project "$PROJECT" --configuration Release -- \
  echo-review-verify --base "$BASE" "$ECHO_REVIEW"
