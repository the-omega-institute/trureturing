#!/usr/bin/env bash
set -euo pipefail

readonly script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly controller_root="$(cd "$script_dir/../../.." && pwd -P)"
readonly assembly="$controller_root/tools/StrataLint.EngineeringScope/bin/Release/net10.0/StrataLint.EngineeringScope.dll"
readonly classifier="$script_dir/pure-revert-detect.sh"

if (( $# < 1 )); then
  printf '%s\n' 'SELF_LOCK_PROBE_BAD_ARGUMENT' >&2
  exit 2
fi
if [[ ! -f "$assembly" || ! -f "$classifier" ]]; then
  printf '%s\n' 'SELF_LOCK_PROBE_CONTROLLER_UNAVAILABLE' >&2
  exit 2
fi

command="$1"
shift
case "$command" in
  evaluator-digest)
    (( $# == 0 )) || { printf '%s\n' 'SELF_LOCK_PROBE_BAD_ARGUMENT' >&2; exit 2; }
    exec dotnet "$assembly" self-lock-probe evaluator-digest --controller-root "$controller_root"
    ;;
  evaluate)
    exec dotnet "$assembly" self-lock-probe evaluate \
      --controller-root "$controller_root" \
      --pure-revert-script "$classifier" \
      "$@"
    ;;
  *)
    printf '%s\n' 'SELF_LOCK_PROBE_BAD_ARGUMENT' >&2
    exit 2
    ;;
esac
