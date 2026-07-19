#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
BASE="${1:-origin/dev}"
REPORT="$ROOT/.lake/build/stratalint/raw-lean-report.json"
CONSUMER="$ROOT/Meta/StrataLint/scripts/report/report-consumer.sh"
PROJECT="$ROOT/Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj"

cd "$ROOT"
exec "$CONSUMER" --role ingest-consumer --report "$REPORT" -- \
  dotnet run --project "$PROJECT" --configuration Release -- ingest --base "$BASE"
