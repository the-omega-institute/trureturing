#!/usr/bin/env bash
set -euo pipefail

export PATH="$HOME/.elan/bin:/usr/local/share/dotnet:/opt/homebrew/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin:${PATH:-}"

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
RECENT="${1:-10}"
LEDGER="${STRATALINT_PERF_LEDGER:-$HOME/.stratalint-perf/events.jsonl}"

exec dotnet run \
  --project "$ROOT/Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj" \
  --configuration Release \
  -- \
  perf-report --ledger "$LEDGER" --recent "$RECENT"
