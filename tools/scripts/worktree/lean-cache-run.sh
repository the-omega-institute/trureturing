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
  cli=(dotnet run --project "$ROOT/tools/StrataLint.Lean/StrataLint.Lean.csproj" --configuration Release --)
fi
donor=()
[[ -z "${STRATALINT_LEAN_CACHE_DONOR_REPOSITORY:-}" ]] || donor=(--donor-repository "$STRATALINT_LEAN_CACHE_DONOR_REPOSITORY")
if [[ "$1" == --build ]]; then
  shift
  root_targets=() impl_targets=() reg_targets=()
  for target in "$@"; do
    case "$target" in
      Reg|Reg.*|Reg:*|+Reg.*|@reg|@reg/*|@reg:*|LeanInformationAuditRegTests*|LeanInformationAuditRegAnalysis*|+LeanInformationAuditReg*) reg_targets+=("$target") ;;
      LeanInformationAudit*|+LeanInformationAudit*|leanInspector/*|leanInspectorInterface/*|@leanInspector|@leanInspector/*|@leanInspector:*|@leanInspectorInterface|@leanInspectorInterface/*|@leanInspectorInterface:*) impl_targets+=("$target") ;;
      *) root_targets+=("$target") ;;
    esac
  done
  if [[ $# == 0 || ${#root_targets[@]} != 0 ]]; then
    "${cli[@]}" with-cache-reader ${donor[@]+"${donor[@]}"} -- lake build ${root_targets[@]+"${root_targets[@]}"}
  fi
  if [[ $# == 0 || ${#impl_targets[@]} != 0 ]]; then
    "${cli[@]}" with-cache-reader ${donor[@]+"${donor[@]}"} -- lake -d "$ROOT/tools/lean-inspector" build ${impl_targets[@]+"${impl_targets[@]}"}
  fi
  if [[ ${#reg_targets[@]} != 0 || ( $# == 0 && -f "$ROOT/Reg/lakefile.toml" ) ]]; then
    "${cli[@]}" with-cache-reader ${donor[@]+"${donor[@]}"} -- lake -d "$ROOT/Reg" build ${reg_targets[@]+"${reg_targets[@]}"}
  fi
  exit 0
fi
exec "${cli[@]}" with-cache-reader ${donor[@]+"${donor[@]}"} -- "$@"
