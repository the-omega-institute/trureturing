#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
SOLUTION="$ROOT/Meta/StrataLint/StrataLint.sln"

dotnet restore "$SOLUTION" --locked-mode
dotnet build "$SOLUTION" --no-restore --configuration Release --warnaserror
