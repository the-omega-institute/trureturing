#!/usr/bin/env bash
set -euo pipefail

if [[ "$#" -ne 3 || -z "$1" || -z "$2" || -z "$3" ]]; then
  printf '%s\n' 'usage: engineering-tests.sh <repository> <head> <base>' >&2
  exit 2
fi

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
REPOSITORY="$1"
HEAD="$2"
BASE="$3"

cd "$REPOSITORY" && dotnet run --project "$HERE/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj" --configuration Release --no-launch-profile -- --repository "$REPOSITORY" --head "$HEAD" --base "$BASE"
