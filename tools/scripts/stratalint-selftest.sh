#!/usr/bin/env bash
set -uo pipefail

if ! ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"; then
  printf '%s\n' 'STRATALINT_SELFTEST_INFRASTRUCTURE operation=resolve-root exit=2' >&2
  exit 2
fi
PROJECT="$ROOT/tools/StrataLint.Cli/StrataLint.Cli.csproj"
if ! RUNS="$(mktemp -d)"; then
  printf '%s\n' 'STRATALINT_SELFTEST_INFRASTRUCTURE operation=create-temporary-directory exit=2' >&2
  exit 2
fi

cleanup() {
  rm -rf -- "$RUNS"
}
trap cleanup EXIT HUP INT TERM

if ! cd "$ROOT"; then
  printf '%s\n' 'STRATALINT_SELFTEST_INFRASTRUCTURE operation=enter-root exit=2' >&2
  exit 2
fi
first_status=0
dotnet run --project "$PROJECT" --configuration Release -- selftest > "$RUNS/first.txt" || first_status=$?
if [[ "$first_status" -ne 0 ]]; then
  printf 'STRATALINT_SELFTEST_INFRASTRUCTURE operation=run-first exit=%s\n' "$first_status" >&2
  exit 2
fi
second_status=0
dotnet run --project "$PROJECT" --configuration Release -- selftest > "$RUNS/second.txt" || second_status=$?
if [[ "$second_status" -ne 0 ]]; then
  printf 'STRATALINT_SELFTEST_INFRASTRUCTURE operation=run-second exit=%s\n' "$second_status" >&2
  exit 2
fi
compare_status=0
cmp "$RUNS/first.txt" "$RUNS/second.txt" || compare_status=$?
if [[ "$compare_status" -eq 1 ]]; then
  printf '%s\n' 'STRATALINT_SELFTEST_MISMATCH comparison=byte-for-byte exit=1' >&2
  exit 1
elif [[ "$compare_status" -ne 0 ]]; then
  printf 'STRATALINT_SELFTEST_INFRASTRUCTURE operation=compare exit=%s\n' "$compare_status" >&2
  exit 2
fi
if ! cat "$RUNS/first.txt"; then
  printf '%s\n' 'STRATALINT_SELFTEST_INFRASTRUCTURE operation=emit exit=2' >&2
  exit 2
fi
