#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd -P)"
FILE="${1:-}"
BASE="${2:-origin/dev}"
PROJECT="$ROOT/Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj"

arguments=(echo-verify --base "$BASE" --if-affected)
if [[ -n "$FILE" ]]; then
  arguments=(echo-verify --file "$FILE" --base "$BASE" --if-affected)
fi
cd "$ROOT"
exec dotnet run --project "$PROJECT" --configuration Release -- \
  "${arguments[@]}"
