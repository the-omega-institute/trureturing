#!/bin/bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
cd "$ROOT"
stage="${1:-}"
PLAN_PATH="${CI_PLAN_PATH:-}"
CHANGES_PATH="${CI_CHANGES_PATH:-}"
if [[ -n "${CI_PLAN_B64:-}" || -n "${CI_CHANGES_B64:-}" ]]; then
  PLAN_PATH="$ROOT/build/ci/plan.json"
  CHANGES_PATH="$ROOT/build/ci/changes.json"
fi
completed=0
runner=tools/StrataLint.EngineeringScope/bin/Release/net10.0/StrataLint.EngineeringScope.dll
finish() {
  local raw=$?
  trap - EXIT
  local rc=2
  case "$raw" in 0|1|2) rc="$raw" ;; esac
  [[ "$raw" != 0 || "$completed" == 1 ]] || rc=2
  printf 'CI_STAGE_RESULT stage=%s exit=%s raw_exit=%s\n' "$stage" "$rc" "$raw"
  exit "$rc"
}
trap finish EXIT
trap 'exit 2' HUP INT TERM
case "$stage" in
  build|engineering|current) [[ $# == 1 ]] || exit 2 ;;
  delta) [[ $# == 2 ]] || exit 2 ;;
  *) exit 2 ;;
esac
if [[ -n "${PREFLIGHT_DEADLINE_AT:-}" ]]; then
  [[ "$PREFLIGHT_DEADLINE_AT" =~ ^[0-9]{1,11}$ ]] || exit 2
  [[ "$PREFLIGHT_DEADLINE_AT" -gt "$(date +%s)" ]] || { echo 'PREFLIGHT_BUDGET_EXHAUSTED owner=outer-deadline' >&2; exit 2; }
fi
stage_options=()
if [[ -n "$PLAN_PATH" || -n "$CHANGES_PATH" ]]; then
  stage_options+=(--plan "$PLAN_PATH" --changes "$CHANGES_PATH")
fi
input_options=()
[[ "$stage" != delta ]] || input_options+=(--base "$2")
input_rc=0
python3 -B tools/scripts/workflow/ci.py stage-input --repository "$ROOT" --stage "$stage" \
  --allow-direct --dispatch ${stage_options[@]+"${stage_options[@]}"} ${input_options[@]+"${input_options[@]}"} || input_rc=$?
case "$input_rc" in 0) completed=1; exit 0 ;; 10) ;; *) exit 2 ;; esac
case "$stage" in
  build|engineering)
    export CI=true DOTNET_CLI_UI_LANGUAGE=en-US
    if [[ "$stage" == engineering && -n "${CI_BUILD_ROUND:-}" ]]; then
      [[ -f "$runner" ]] || exit 2
      dotnet "$runner" "$stage" --repository "$ROOT" ${stage_options[@]+"${stage_options[@]}"} --build-round "$CI_BUILD_ROUND"
      completed=1
      exit 0
    fi
    python3 tools/scripts/report/dotnet_producer.py prepare "$ROOT"
    export CustomAfterMicrosoftCSharpTargets="$ROOT/build/judge-seed/seed.targets"
    # Bootstrap nodes belong to these invocations and must release their output.
    /bin/bash tools/scripts/report/report-supervisor.sh --role ci-bootstrap-restore -- \
      dotnet restore tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj --locked-mode -nr:false
    # Match the solution's import graph so its bootstrap compiler seed is reusable.
    /bin/bash tools/scripts/report/report-supervisor.sh --role ci-bootstrap-build -- \
      dotnet build tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj --configuration Release --no-restore --warnaserror -nr:false \
        -p:CustomAfterMicrosoftCommonTargets="$ROOT/tools/scripts/ci-build-outputs.targets"
    dotnet "$runner" "$stage" --repository "$ROOT" ${stage_options[@]+"${stage_options[@]}"}
    ;;
  current)
    [[ -f "$runner" ]] || exit 2
    dotnet "$runner" current --repository "$ROOT" ${stage_options[@]+"${stage_options[@]}"}
    ;;
  delta)
    [[ -f "$runner" ]] || exit 2
    dotnet "$runner" delta --repository "$ROOT" --base "$2" ${stage_options[@]+"${stage_options[@]}"}
    ;;
  *) exit 2 ;;
esac
completed=1
