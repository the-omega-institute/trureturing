#!/bin/bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"

dotnet test Meta/StrataLint/StrataLint.sln --configuration Release --verbosity normal
"$ROOT/.fkst/scripts/run.sh" test
