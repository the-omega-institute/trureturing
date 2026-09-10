#!/bin/bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
cd "$ROOT"
stage="${1:-}"
runner=tools/StrataLint.EngineeringScope/bin/Release/net10.0/StrataLint.EngineeringScope.dll
finish() {
  local raw=$?
  trap - EXIT
  local rc=2
  case "$raw" in 0|1|2) rc="$raw" ;; esac
  printf 'CI_STAGE_RESULT stage=%s exit=%s raw_exit=%s\n' "$stage" "$rc" "$raw"
  exit "$rc"
}
trap finish EXIT
trap 'exit 2' HUP INT TERM
if [[ -n "${PREFLIGHT_DEADLINE_AT:-}" ]]; then
  [[ "$PREFLIGHT_DEADLINE_AT" =~ ^[0-9]{1,11}$ ]] || exit 2
  [[ "$PREFLIGHT_DEADLINE_AT" -gt "$(date +%s)" ]] || { echo 'PREFLIGHT_BUDGET_EXHAUSTED owner=outer-deadline' >&2; exit 2; }
fi
case "$stage" in
  build|engineering)
    [[ $# == 1 ]] || exit 2
    export CI=true
    if [[ "$stage" == engineering && -n "${CI_BUILD_ROUND:-}" ]]; then
      [[ -f "$runner" ]] || exit 2
      dotnet "$runner" "$stage" --repository "$ROOT" --build-round "$CI_BUILD_ROUND"
      exit $?
    fi
    /bin/bash tools/scripts/report/report-supervisor.sh --role ci-bootstrap-restore -- \
      dotnet restore tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj --locked-mode
    /bin/bash tools/scripts/report/report-supervisor.sh --role ci-bootstrap-build -- \
      dotnet build tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj --configuration Release --no-restore --warnaserror
    dotnet "$runner" "$stage" --repository "$ROOT"
    ;;
  current)
    [[ $# == 1 && -f "$runner" ]] || exit 2
    dotnet "$runner" current --repository "$ROOT"
    ;;
  delta)
    [[ $# == 2 && -f "$runner" ]] || exit 2
    dotnet "$runner" delta --repository "$ROOT" --base "$2"
    ;;
  *) exit 2 ;;
esac
