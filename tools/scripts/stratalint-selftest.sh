#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
PROJECT="$ROOT/tools/StrataLint.Cli/StrataLint.Cli.csproj"
RUNS="$(mktemp -d)"

cleanup() {
  rm -rf -- "$RUNS"
}
trap cleanup EXIT HUP INT TERM

cd "$ROOT"
restore_args=()
[[ "${CI_DOTNET_PREPARED:-0}" != 1 ]] || restore_args=(--no-restore)
dotnet run --project "$PROJECT" ${restore_args[@]+"${restore_args[@]}"} --configuration Release -- selftest > "$RUNS/first.txt"
dotnet run --project "$PROJECT" ${restore_args[@]+"${restore_args[@]}"} --configuration Release -- selftest > "$RUNS/second.txt"
cmp "$RUNS/first.txt" "$RUNS/second.txt"
cat "$RUNS/first.txt"
