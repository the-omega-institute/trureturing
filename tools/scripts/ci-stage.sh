#!/bin/bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
cd "$ROOT"
stage="${1:-}"
PLAN_PATH="${CI_PLAN_PATH:-}"
CHANGES_PATH="${CI_CHANGES_PATH:-}"
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
seed_options=()
if [[ "$stage" == engineering || "$stage" == current ]]; then
  case "${CI_SEED_EXPORT-automatic}" in automatic|deferred) ;; *) exit 2 ;; esac
  seed_options+=(--seed-export "${CI_SEED_EXPORT-automatic}")
fi
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
      dotnet "$runner" "$stage" --repository "$ROOT" ${stage_options[@]+"${stage_options[@]}"} ${seed_options[@]+"${seed_options[@]}"} --build-round "$CI_BUILD_ROUND"
      completed=1
      exit 0
    fi
    python3 tools/scripts/report/dotnet_producer.py prepare "$ROOT"
    export CustomAfterMicrosoftCSharpTargets="$ROOT/build/judge-seed/seed.targets"
    # compiler-logger / CI_CSC_LOGGER_ASSEMBLY carry only this run's diagnostic
    # address, not work selection or cache validity. The helper's own bootstrap
    # precedes this logger and is outside its counts. Always replace an inherited
    # address, including after an optional seed miss.
    CI_CSC_LOGGER_ASSEMBLY=
    if ! CI_CSC_LOGGER_ASSEMBLY="$(python3 tools/scripts/report/dotnet_producer.py compiler-logger "$ROOT")"; then
      CI_CSC_LOGGER_ASSEMBLY=
    fi
    export CI_CSC_LOGGER_ASSEMBLY
    compiler_observation=()
    if [[ -n "$CI_CSC_LOGGER_ASSEMBLY" && -f "$CI_CSC_LOGGER_ASSEMBLY" ]]; then
      compiler_observation+=("-logger:StrataLint.JudgeSeed.CscExecutionLogger,$CI_CSC_LOGGER_ASSEMBLY")
    else
      echo 'JUDGE_CSC {"status":"unavailable","count":null}'
    fi
    # Bootstrap nodes belong to these invocations and must release their output.
    /bin/bash tools/scripts/report/report-supervisor.sh --role ci-bootstrap-restore -- \
      dotnet restore tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj --locked-mode -nr:false
    # Match the solution's import graph so its bootstrap compiler seed is reusable.
    /bin/bash tools/scripts/report/report-supervisor.sh --role ci-bootstrap-build -- \
      dotnet build tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj --configuration Release --no-restore --warnaserror -nr:false \
        -p:CustomAfterMicrosoftCommonTargets="$ROOT/tools/scripts/ci-build-outputs.targets" ${compiler_observation[@]+"${compiler_observation[@]}"}
    dotnet "$runner" "$stage" --repository "$ROOT" ${stage_options[@]+"${stage_options[@]}"} ${seed_options[@]+"${seed_options[@]}"}
    ;;
  current)
    [[ -f "$runner" ]] || exit 2
    source tools/scripts/lib/resource-observation-lib.sh
    # Keep the stage's cancellation traps outside the sampler's signal scope.
    (resource_observe_run_periodic dotnet "$runner" current --repository "$ROOT" ${stage_options[@]+"${stage_options[@]}"} ${seed_options[@]+"${seed_options[@]}"})
    ;;
  delta)
    [[ -f "$runner" ]] || exit 2
    dotnet "$runner" delta --repository "$ROOT" --base "$2" ${stage_options[@]+"${stage_options[@]}"}
    ;;
  *) exit 2 ;;
esac
completed=1
