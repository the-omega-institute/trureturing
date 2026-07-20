#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd -P)"
FILE="${1:-}"
BASE="${2:-origin/dev}"
PROJECT="$ROOT/Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj"

[[ -n "$FILE" ]] || { echo "echo-verify: FILE is required" >&2; exit 2; }
cd "$ROOT"
exec dotnet run --project "$PROJECT" --configuration Release -- \
  echo-verify --file "$FILE" --base "$BASE" --if-affected
