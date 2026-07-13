#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
PROJECT="$ROOT/Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj"
RUNS="$(mktemp -d)"

cleanup() {
  rm -rf -- "$RUNS"
}
trap cleanup EXIT HUP INT TERM

cd "$ROOT"
dotnet run --project "$PROJECT" --configuration Release -- selftest > "$RUNS/first.txt"
dotnet run --project "$PROJECT" --configuration Release -- selftest > "$RUNS/second.txt"
cmp "$RUNS/first.txt" "$RUNS/second.txt"
cat "$RUNS/first.txt"
