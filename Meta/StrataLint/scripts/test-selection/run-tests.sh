#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 3 || ! -f "$3" ]]; then
  printf '%s\n' "usage: run-tests.sh <repository-root> <pull-request|dev-push> <changed-paths-file>" >&2
  exit 2
fi

repository_root="$1"
event_kind="$2"
changed_paths_file="$3"
changed_paths=()
while IFS= read -r changed_path || [[ -n "$changed_path" ]]; do
  changed_paths+=("$changed_path")
done < "$changed_paths_file"
projects_output="$(
  dotnet run --no-build \
    --project "$repository_root/Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj" \
    --configuration Release -- select-tests --event "$event_kind" "${changed_paths[@]}"
)"

while IFS= read -r project; do
  [[ -n "$project" ]] || continue
  dotnet test "$repository_root/$project" --no-build --configuration Release --verbosity normal
done <<< "$projects_output"
