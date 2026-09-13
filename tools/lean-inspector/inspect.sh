#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
REPOSITORY="" OUTPUT="" LOG_DIR=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --repository|--output|--log-dir)
      [[ $# -ge 2 && -n "$2" ]] || { echo "inspect.sh: $1 requires a value" >&2; exit 2; }
      case "$1" in
        --repository) REPOSITORY="$2" ;;
        --output) OUTPUT="$2" ;;
        --log-dir) LOG_DIR="$2" ;;
      esac
      shift 2 ;;
    *) echo "inspect.sh: unknown argument '$1'" >&2; exit 2 ;;
  esac
done
[[ -n "$REPOSITORY" && -d "$REPOSITORY" && -n "$OUTPUT" ]] \
  || { echo 'inspect.sh: --repository ROOT --output FILE are required' >&2; exit 2; }
REPOSITORY="$(cd "$REPOSITORY" && pwd -P)"
[[ "$OUTPUT" == /* ]] || OUTPUT="$REPOSITORY/$OUTPUT"
[[ -n "$LOG_DIR" ]] || LOG_DIR="${OUTPUT}.logs"
[[ "$LOG_DIR" == /* ]] || LOG_DIR="$REPOSITORY/$LOG_DIR"
LAKE="${LAKE_BIN:-$(command -v lake || true)}"
[[ -n "$LAKE" && "$LAKE" == /* && -x "$LAKE" ]] \
  || { echo 'inspect.sh: an absolute executable lake path is required (LAKE_BIN)' >&2; exit 2; }

# This entry owns supervision as well as production, including direct callers.
if [[ "${STRATALINT_INSPECTOR_SUPERVISED:-0}" != 1 ]]; then
  exec "$SCRIPT_DIR/../scripts/report/report-supervisor.sh" --role lean-producer --lean-slot -- \
    env STRATALINT_INSPECTOR_SUPERVISED=1 LAKE_BIN="$LAKE" \
    "$SCRIPT_DIR/inspect.sh" --repository "$REPOSITORY" --output "$OUTPUT" --log-dir "$LOG_DIR"
fi
mkdir -p "$(dirname "$OUTPUT")" "$LOG_DIR"
export STRATALINT_INSPECTOR_ACTIVITY="$LOG_DIR/native-work.jsonl"
: > "$STRATALINT_INSPECTOR_ACTIVITY"
source "$SCRIPT_DIR/../scripts/lib/resource-observation-lib.sh"
resource_observe lean-inspector-start "$REPOSITORY" || true
finish() { local rc=$?; trap - EXIT; resource_observe lean-inspector-finish "$REPOSITORY" || true; exit "$rc"; }
trap finish EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

run_phase() {
  local phase="$1" status=0
  shift
  (cd "$REPOSITORY" && "$@") > "$LOG_DIR/$phase.stdout.log" 2> "$LOG_DIR/$phase.stderr.log" || status=$?
  printf '%s\n' "$status" > "$LOG_DIR/$phase.exit.log"
  if [[ "$status" != 0 ]]; then
    printf 'LEAN_INSPECTOR_FAILED phase=%s exit=%s\n' "$phase" "$status" >&2
    cat "$LOG_DIR/$phase.stdout.log" "$LOG_DIR/$phase.stderr.log" >&2
    return "$status"
  fi
}

# Validate required authored inputs before provisioning or consuming artifacts.
run_phase inputs python3 "$SCRIPT_DIR/../scripts/report/lean-report-selection.py" validate --repository "$REPOSITORY"
run_phase utility-input-build dotnet build "$SCRIPT_DIR/../StrataLint.Cli/StrataLint.Cli.csproj" \
  --configuration Release --nologo --verbosity quiet
run_phase ensure /bin/bash "$REPOSITORY/tools/scripts/worktree/lean-cache-ensure.sh"
# The package facet demands all ordinary defaults/audits and owns module work.
# The guarded reader retains the existing compiler/cache policy and concurrency.
run_phase report "$REPOSITORY/tools/scripts/worktree/lean-cache-run.sh" "$LAKE" build :report
run_phase publish python3 "$SCRIPT_DIR/native.py" publish "$REPOSITORY" "$OUTPUT"
cat "$LOG_DIR/publish.stdout.log"
