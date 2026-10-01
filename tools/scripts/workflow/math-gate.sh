#!/bin/bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
cd "$ROOT"
make lean-report
dotnet build tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -nologo
CLI=tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll
dotnet "$CLI" check-current --candidate-lean-report .lake/build/stratalint/raw-lean-report.json
