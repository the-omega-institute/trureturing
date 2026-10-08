#!/usr/bin/env bash
set -euo pipefail

# Build the full solution unless a project path is supplied.
[[ $# -le 1 ]] || { echo 'usage: dotnet-build.sh [PROJECT]' >&2; exit 2; }
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
BUILD_TARGET="${1:-$ROOT/tools/StrataLint.sln}"
[[ "$BUILD_TARGET" == /* ]] || BUILD_TARGET="$ROOT/$BUILD_TARGET"

dotnet restore "$BUILD_TARGET" --locked-mode
dotnet build "$BUILD_TARGET" --no-restore --configuration Release --warnaserror
