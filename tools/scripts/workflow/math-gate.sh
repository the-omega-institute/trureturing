#!/bin/bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
cd "$ROOT"
PATHS_FILE="$(mktemp "${TMPDIR:-/tmp}/math-gate-paths.XXXXXXXX")"
trap 'rm -f -- "$PATHS_FILE"' EXIT
git diff --name-only -z "${BASE:-origin/dev}" -- > "$PATHS_FILE"
git ls-files --others --exclude-standard -z >> "$PATHS_FILE"
make lean-report
dotnet build tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -nologo
CLI=tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll
dotnet "$CLI" check-current --candidate-lean-report .lake/build/stratalint/raw-lean-report.json --scribe-paths-from "$PATHS_FILE"
