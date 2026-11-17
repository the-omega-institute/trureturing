#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
cd "$ROOT"
[[ "${RETIRE_MODE:-archive}" == archive || "${RETIRE_MODE:-}" == delete ]] || { echo 'MODE must be archive or delete' >&2; exit 2; }
[[ "${RETIRE_WRITE:-0}" == 0 || "${RETIRE_WRITE:-}" == 1 ]] || { echo 'WRITE must be 0 or 1' >&2; exit 2; }
read -r -a sources <<< "${RETIRE_SOURCES:-}"
[[ ${#sources[@]} -gt 0 ]] || { echo 'SOURCES is required' >&2; exit 2; }
args=(retire-sources --mode "${RETIRE_MODE:-archive}")
for source in "${sources[@]}"; do args+=(--source "$source"); done
project=tools/StrataLint.Cli/StrataLint.Cli.csproj
dotnet build "$project" --configuration Release -p:RestoreLockedMode=true -nologo --verbosity quiet >&2
targets="$(dotnet run --no-build --project "$project" --configuration Release -- "${args[@]}" --lean-inputs)"
if [[ -n "$targets" ]]; then
    report="$ROOT/.lake/build/stratalint/retirement-lean-report.json"
    make lean-report-scoped "LEAN_TARGETS=$targets" "LEAN_REPORT=$report"
    export STRATALINT_LEAN_REPORT="$report"
fi
if [[ "${RETIRE_WRITE:-0}" == 1 ]]; then args+=(--write); fi
dotnet run --no-build --project "$project" --configuration Release -- "${args[@]}"
