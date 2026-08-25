#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
VERB="${1:-}"
BASE="${2:-}"
REPORT="$ROOT/.lake/build/stratalint/raw-lean-report.json"
CONSUMER="$ROOT/tools/scripts/report/report-consumer.sh"
PROJECT="$ROOT/tools/StrataLint.Cli/StrataLint.Cli.csproj"

cd "$ROOT"
[[ -n "$BASE" ]] || { echo "USAGE: ingest.sh ingest BASE" >&2; exit 2; }
case "$VERB" in
  ingest)
    exec "$CONSUMER" --role ingest-consumer --report "$REPORT" -- \
      dotnet run --project "$PROJECT" --configuration Release -- ingest --base "$BASE"
    ;;
  *)
    echo "USAGE: ingest.sh ingest BASE" >&2
    exit 2
    ;;
esac
