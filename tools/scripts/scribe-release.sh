#!/usr/bin/env bash
# Requires Bash, Git and the .NET SDK selected by the repository's global.json.
set -euo pipefail

fail() {
  printf 'SCRIBE_RELEASE %s\n' "$2" >&2
  exit "$1"
}

[[ "$#" -eq 0 ]] || fail 2 'InvalidArguments: usage: scribe-release.sh'
for tool in git dotnet cat dirname; do
  command -v "$tool" >/dev/null 2>&1 || fail 2 "MissingTool: $tool"
done
ROOT="$(cd "$(dirname "$0")/../.." && pwd -P)"
PROJECT="$ROOT/tools/StrataLint.Scribe.Documents/StrataLint.Scribe.Documents.csproj"
[[ -f "$ROOT/global.json" && -f "$PROJECT" && -d "$ROOT/Blueprint" ]] \
  || fail 2 'InvalidRepository: global.json, Blueprint and the documents host are required'
cd "$ROOT"
git --version >/dev/null || fail 2 'GitUnavailable'
dotnet --version >/dev/null || fail 2 'SdkUnavailable: install the SDK selected by global.json'
[[ "$(git rev-parse --show-toplevel)" == "$ROOT" ]] || fail 2 'InvalidRepositoryRoot'
status="$(git status --porcelain)" || fail 2 'GitStatusFailed'
[[ -z "$status" ]] || fail 1 'DirtyWorktree: commit or remove local changes before release'
SOURCE_COMMIT="$(git rev-parse --verify HEAD)" || fail 2 'SourceCommitUnavailable'
[[ "$SOURCE_COMMIT" =~ ^[0-9a-f]{40}$ ]] || fail 2 'InvalidSourceCommit'
DIRECTORY="$ROOT/Generated/scribe-release/$SOURCE_COMMIT"

if [[ ! -e "$DIRECTORY" && ! -L "$DIRECTORY" ]]; then
  if dotnet run --project "$PROJECT" --configuration Release -- \
      resources release --source-commit "$SOURCE_COMMIT" --out "$DIRECTORY"; then
    :
  else
    fail "$?" 'ReleaseFailed'
  fi
fi
if dotnet run --project "$PROJECT" --configuration Release -- \
    resources verify-release --dir "$DIRECTORY" --source-commit "$SOURCE_COMMIT"; then
  :
else
  fail "$?" 'VerificationFailed'
fi
cat "$DIRECTORY/identity.json"
printf '\n'
