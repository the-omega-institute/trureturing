#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
VERB="${1:-}"
BASE="${2:-}"
REPORT="$ROOT/.lake/build/stratalint/raw-lean-report.json"
CONSUMER="$ROOT/tools/scripts/report/report-consumer.sh"
PROJECT="$ROOT/tools/StrataLint.Cli/StrataLint.Cli.csproj"

cd "$ROOT"
[[ -n "$BASE" ]] || { echo "USAGE: ingest.sh ingest|realign-receipts BASE" >&2; exit 2; }
case "$VERB" in
  ingest)
    exec "$CONSUMER" --role ingest-consumer --report "$REPORT" -- \
      dotnet run --project "$PROJECT" --configuration Release -- ingest --base "$BASE"
    ;;
  realign-receipts)
    echo "realign-receipts: a local caller cannot authenticate a protected baseline; " \
      "the base-owned caller must supply an exact OID directly to --protected-base-oid" >&2
    exit 2
    ;;
  *)
    echo "USAGE: ingest.sh ingest|realign-receipts BASE" >&2
    exit 2
    ;;
esac
