#!/usr/bin/env bash
# Requires Bash and the .NET SDK selected by the repository's global.json.
set -euo pipefail

fail() {
  printf 'SCRIBE_RELEASE %s\n' "$2" >&2
  exit "$1"
}

[[ "$#" -eq 0 ]] || fail 2 'InvalidArguments: usage: scribe-release.sh'
command -v dotnet >/dev/null 2>&1 || fail 2 'MissingTool: dotnet'
ROOT="$(cd "$(dirname "$0")/../.." && pwd -P)"
PROJECT="$ROOT/tools/StrataLint.Scribe.Documents/StrataLint.Scribe.Documents.csproj"
[[ -f "$ROOT/global.json" && -f "$PROJECT" && -d "$ROOT/Blueprint" ]] \
  || fail 2 'InvalidRepository: global.json, Blueprint and the documents host are required'
cd "$ROOT"
dotnet --version >/dev/null || fail 2 'SdkUnavailable: install the SDK selected by global.json'
DIRECTORY="$ROOT/Generated/scribe-release"
rm -rf -- "$DIRECTORY"
dotnet run --project "$PROJECT" --configuration Release -- \
  resources release --out "$DIRECTORY" \
  || fail "$?" 'ReleaseFailed'
dotnet run --project "$PROJECT" --configuration Release -- \
  resources verify-release --dir "$DIRECTORY" \
  || fail "$?" 'VerificationFailed'
printf 'SCRIBE_RELEASE verified %s\n' "$DIRECTORY"
