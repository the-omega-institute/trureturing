#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
[[ $# -gt 0 ]] || { echo 'lean-cache-run: COMMAND is required' >&2; exit 2; }
cd "$ROOT"
# Lake checks each pinned Git dependency with `git diff --exit-code HEAD`.
# Restoring the dependency files changes their stat data, so Git's optional
# index refresh would change an otherwise identical cache. Keep the content
# comparison and required writes (such as checkout), but disable that refresh
# for this process tree. Append to, rather than replace, caller configuration.
git_config_count="${GIT_CONFIG_COUNT:-0}"
[[ "$git_config_count" =~ ^[0-9]+$ ]] || { echo 'lean-cache-run: invalid GIT_CONFIG_COUNT' >&2; exit 2; }
while [[ ${#git_config_count} -gt 1 && "$git_config_count" == 0* ]]; do
  git_config_count="${git_config_count#0}"
done
# Git accepts a signed int count; leave room for the appended entry.
if [[ ${#git_config_count} -gt 10 ]] || (( 10#$git_config_count >= 2147483647 )); then
  echo 'lean-cache-run: GIT_CONFIG_COUNT cannot be extended' >&2
  exit 2
fi
export "GIT_CONFIG_KEY_${git_config_count}=diff.autoRefreshIndex"
export "GIT_CONFIG_VALUE_${git_config_count}=false"
export GIT_CONFIG_COUNT="$((git_config_count + 1))"
if [[ -n "${STRATALINT_LEAN_PRODUCER_DLL:-}" ]]; then
  [[ "$STRATALINT_LEAN_PRODUCER_DLL" == /* && -f "$STRATALINT_LEAN_PRODUCER_DLL" ]] || { echo 'lean-cache-run: candidate producer DLL is absent' >&2; exit 2; }
  cli=(dotnet "$STRATALINT_LEAN_PRODUCER_DLL")
else
  # Reused MSBuild nodes can hold these output pipes after the producer exits.
  export MSBUILDDISABLENODEREUSE=1
  cli=(dotnet run --project "$ROOT/tools/StrataLint.Lean/StrataLint.Lean.csproj" --configuration Release --)
fi
donor=()
[[ -z "${STRATALINT_LEAN_CACHE_DONOR_REPOSITORY:-}" ]] || donor=(--donor-repository "$STRATALINT_LEAN_CACHE_DONOR_REPOSITORY")
exec "${cli[@]}" with-cache-reader ${donor[@]+"${donor[@]}"} -- "$@"
