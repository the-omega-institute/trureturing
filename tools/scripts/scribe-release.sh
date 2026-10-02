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
inputs="$(git ls-files --others -- Blueprint Golden/Projection)" || fail 2 'GitReleaseInputsFailed'
[[ -z "$inputs" ]] || fail 1 'UntrackedReleaseInput: remove untracked or ignored files from Blueprint and Golden/Projection'
SOURCE_COMMIT="$(git rev-parse --verify HEAD)" || fail 2 'SourceCommitUnavailable'
[[ "$SOURCE_COMMIT" =~ ^[0-9a-f]{40}$ ]] || fail 2 'InvalidSourceCommit'
DIRECTORY="$ROOT/Generated/scribe-release/$SOURCE_COMMIT"
PATHS_FILE="$(mktemp "${TMPDIR:-/tmp}/scribe-paths.XXXXXX")" || fail 2 'DefinitionPathsTemporaryFileFailed'
TREE_FILE="$(mktemp "${TMPDIR:-/tmp}/scribe-tree.XXXXXX")" || fail 2 'SourceTreeTemporaryFileFailed'
trap 'rm -f "$PATHS_FILE" "$TREE_FILE"' EXIT
git ls-tree -r -z "$SOURCE_COMMIT" > "$TREE_FILE" || fail 2 'GitSourceTreeFailed'
dotnet run --project "$PROJECT" --configuration Release -- \
    resources verify-source --tree-from "$TREE_FILE" \
  || fail "$?" 'SourceContentMismatch: disk bytes do not match source commit'
tree_paths="$(git ls-tree -r --name-only "$SOURCE_COMMIT" -- Blueprint)" || fail 2 'GitDefinitionPathsFailed'
while IFS= read -r path; do
  case "$path" in *.scribe.cs) printf '%s\n' "$path" ;; esac
done <<< "$tree_paths" > "$PATHS_FILE"

if [[ ! -e "$DIRECTORY" && ! -L "$DIRECTORY" ]]; then
  if dotnet run --project "$PROJECT" --configuration Release -- \
      resources release --source-commit "$SOURCE_COMMIT" --out "$DIRECTORY"; then
    :
  else
    fail "$?" 'ReleaseFailed'
  fi
fi
if dotnet run --project "$PROJECT" --configuration Release -- \
    resources verify-release --dir "$DIRECTORY" --source-commit "$SOURCE_COMMIT" --paths-from "$PATHS_FILE"; then
  :
else
  fail "$?" 'VerificationFailed'
fi
cat "$DIRECTORY/identity.json"
printf '\n'
