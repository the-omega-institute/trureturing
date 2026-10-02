#!/usr/bin/env bash
# Requires Bash, Git and the .NET SDK selected by the repository's global.json.
set -euo pipefail

fail() {
  printf 'SCRIBE_RELEASE %s\n' "$2" >&2
  exit "$1"
}

[[ "$#" -eq 0 ]] || fail 2 'InvalidArguments: usage: scribe-release.sh'
for tool in git dotnet cat dirname mktemp rm; do
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
untracked="$(git ls-files --others --exclude-standard)" || fail 2 'GitUntrackedFilesFailed'
[[ -z "$untracked" ]] || fail 1 'UntrackedFiles: commit or remove untracked files before release'
export GIT_NO_REPLACE_OBJECTS=1
git diff --cached --quiet HEAD -- || fail 1 'IndexNotAtHead: the index must match HEAD before release'
SOURCE_COMMIT="$(git rev-parse --verify HEAD)" || fail 2 'SourceCommitUnavailable'
[[ "$SOURCE_COMMIT" =~ ^[0-9a-f]{40}$ ]] || fail 2 'InvalidSourceCommit'
DIRECTORY="$ROOT/Generated/scribe-release/$SOURCE_COMMIT"
COMMIT_FILE=''
TREE_FILE=''
trap 'rm -f "$COMMIT_FILE" "$TREE_FILE"' EXIT
COMMIT_FILE="$(mktemp "${TMPDIR:-/tmp}/scribe-commit.XXXXXX")" || fail 2 'SourceCommitTemporaryFileFailed'
TREE_FILE="$(mktemp "${TMPDIR:-/tmp}/scribe-tree.XXXXXX")" || fail 2 'SourceTreeTemporaryFileFailed'
git cat-file commit "$SOURCE_COMMIT" > "$COMMIT_FILE" || fail 2 'GitSourceCommitFailed'
git ls-tree -r -z "$SOURCE_COMMIT" > "$TREE_FILE" || fail 2 'GitSourceTreeFailed'
dotnet run --project "$PROJECT" --configuration Release -- \
    resources verify-source --source-commit "$SOURCE_COMMIT" --commit-from "$COMMIT_FILE" --tree-from "$TREE_FILE" \
  || fail "$?" 'SourceContentMismatch: disk bytes do not match source commit'

if [[ ! -e "$DIRECTORY" && ! -L "$DIRECTORY" ]]; then
  if dotnet run --project "$PROJECT" --configuration Release -- \
      resources release --source-commit "$SOURCE_COMMIT" --out "$DIRECTORY"; then
    :
  else
    fail "$?" 'ReleaseFailed'
  fi
fi
if dotnet run --project "$PROJECT" --configuration Release -- \
    resources verify-release --dir "$DIRECTORY" --source-commit "$SOURCE_COMMIT" --tree-from "$TREE_FILE"; then
  :
else
  fail "$?" 'VerificationFailed'
fi
cat "$DIRECTORY/identity.json"
printf '\n'
