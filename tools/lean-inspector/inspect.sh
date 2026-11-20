#!/usr/bin/env bash
set -euo pipefail
[[ "${FULL_BUILD:-0}" == 1 ]] || { echo 'full build requires explicit FULL_BUILD=1; use scoped targets instead' >&2; exit 2; }
export LC_ALL=C

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
REPOSITORY="" OUTPUT="" LOG_DIR=""
CACHE_MISS_POLICY=reuse-or-build
REGENERATE_REPORT_ARTIFACTS=0
BUILD_PHASES=()
ACTIVE_PHASE=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --repository|--output|--log-dir|--cache-miss-policy|--regenerate-report-artifacts)
      [[ $# -ge 2 && -n "$2" ]] || { echo "inspect.sh: $1 requires a value" >&2; exit 2; }
      case "$1" in
        --repository) REPOSITORY="$2" ;;
        --output) OUTPUT="$2" ;;
        --log-dir) LOG_DIR="$2" ;;
        --cache-miss-policy) CACHE_MISS_POLICY="$2" ;;
        --regenerate-report-artifacts) REGENERATE_REPORT_ARTIFACTS="$2" ;;
      esac
      shift 2 ;;
    *) echo "inspect.sh: unknown argument '$1'" >&2; exit 2 ;;
  esac
done
case "$CACHE_MISS_POLICY" in
  reuse-or-build|fetch-or-fail|build) ;;
  *) echo 'inspect.sh: --cache-miss-policy requires reuse-or-build, fetch-or-fail or build' >&2; exit 2 ;;
esac
case "$REGENERATE_REPORT_ARTIFACTS" in
  0) ;;
  1) CACHE_MISS_POLICY=build ;;
  *) echo 'inspect.sh: --regenerate-report-artifacts requires 0 or 1' >&2; exit 2 ;;
esac
[[ -n "$REPOSITORY" && -d "$REPOSITORY" && -n "$OUTPUT" ]] \
  || { echo 'inspect.sh: --repository ROOT --output FILE are required' >&2; exit 2; }
REPOSITORY="$(cd "$REPOSITORY" && pwd -P)"
[[ "$OUTPUT" == /* ]] || OUTPUT="$REPOSITORY/$OUTPUT"
[[ -n "$LOG_DIR" ]] || LOG_DIR="${OUTPUT}.logs"
[[ "$LOG_DIR" == /* ]] || LOG_DIR="$REPOSITORY/$LOG_DIR"
# This entry owns supervision as well as production, including direct callers.
if [[ "${STRATALINT_INSPECTOR_SUPERVISED:-0}" != 1 ]]; then
  exec "$SCRIPT_DIR/../scripts/report/report-supervisor.sh" --role lean-producer --lean-slot -- \
    env STRATALINT_INSPECTOR_SUPERVISED=1 \
    "$SCRIPT_DIR/inspect.sh" --repository "$REPOSITORY" --output "$OUTPUT" --log-dir "$LOG_DIR" \
    --cache-miss-policy "$CACHE_MISS_POLICY" --regenerate-report-artifacts "$REGENERATE_REPORT_ARTIFACTS"
fi
BUILD_WORK_FILE="${STRATALINT_LEAN_BUILD_WORK_FILE:-$REPOSITORY/build/lean-cache/build-work.json}"
# Work facts live outside the restored project tree and start empty every call.
rm -f -- "$BUILD_WORK_FILE"
source "$SCRIPT_DIR/../scripts/lib/resource-observation-lib.sh"
resource_observe lean-inspector-start "$REPOSITORY" || true
# Keep diagnostics in a temporary directory until input and optional seed checks complete.
FINAL_LOG_DIR="$LOG_DIR"
STARTUP_LOG_DIR="$(mktemp -d "${TMPDIR:-/tmp}/stratalint-inspector-startup.XXXXXXXX")"
LOG_DIR="$STARTUP_LOG_DIR"
finish() {
  local rc=$?
  trap - EXIT
  if [[ "$rc" == 0 ]]; then
    python3 -B "$SCRIPT_DIR/build_work.py" "$REPOSITORY" "$LOG_DIR" "$BUILD_WORK_FILE" ${BUILD_PHASES[@]+"${BUILD_PHASES[@]}"} || true
  fi
  if [[ "$rc" != 0 ]]; then
    python3 -B "$SCRIPT_DIR/build_work.py" --observations "$LOG_DIR" ${BUILD_PHASES[@]+"${BUILD_PHASES[@]}"} || true
    if [[ -n "$ACTIVE_PHASE" ]]; then
      printf 'LEAN_INSPECTOR_INTERRUPTED phase=%s exit=%s\n' "$ACTIVE_PHASE" "$rc" >&2 || true
      cat "$LOG_DIR/$ACTIVE_PHASE.stdout.log" "$LOG_DIR/$ACTIVE_PHASE.stderr.log" >&2 || true
    fi
    # Direct observations identify the last native boundary even when Lake's
    # buffered output is interrupted. They do not alter the failure verdict.
    if [[ -f "$LOG_DIR/native-phases.jsonl" ]]; then
      cat "$LOG_DIR/native-phases.jsonl" >&2 || true
    fi
  fi
  # Export before a later invocation truncates these local streams. This uses
  # the existing caller log transport on success as well as failure.
  python3 -B "$SCRIPT_DIR/build_work.py" --export "$REPOSITORY" "$LOG_DIR" "$OUTPUT" "$rc" ${BUILD_PHASES[@]+"${BUILD_PHASES[@]}"} || true
  rm -rf -- "$STARTUP_LOG_DIR" || true
  resource_observe lean-inspector-finish "$REPOSITORY" || true
  exit "$rc"
}
trap finish EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

run_phase() {
  local phase="$1" status=0
  local phase_started="${SECONDS:-unavailable}" phase_finished phase_elapsed=unavailable
  shift
  case "$phase" in report) BUILD_PHASES+=("$phase") ;; esac
  # Observations never participate in report reuse or change a phase's verdict.
  [[ "$phase_started" =~ ^[0-9]+$ ]] || phase_started=unavailable
  printf 'LEAN_INSPECTOR_PHASE phase=%s status=started clock=shell-seconds start_seconds=%s\n' \
    "$phase" "$phase_started" >&2 || true
  ACTIVE_PHASE="$phase"
  local budget=()
  if [[ -n "${STRATALINT_CI_COMPUTE_BUDGET:-}" && "${STRATALINT_CI_COMPUTE_ACTIVE:-0}" != 1 ]]; then
    case "$phase" in
      # Native report commands are charged by the cache reader after
      # its own lazy provisioning. These phases must not be charged twice.
      toolchain|report) ;;
      *) budget=(python3 "$REPOSITORY/tools/scripts/workflow/ci_compute.py" run --) ;;
    esac
  fi
  (cd "$REPOSITORY" && ${budget[@]+"${budget[@]}"} "$@") > "$LOG_DIR/$phase.stdout.log" 2> "$LOG_DIR/$phase.stderr.log" || status=$?
  ACTIVE_PHASE=""
  phase_finished="${SECONDS:-unavailable}"
  [[ "$phase_finished" =~ ^[0-9]+$ ]] || phase_finished=unavailable
  if [[ "$phase_started" != unavailable && "$phase_finished" != unavailable ]] \
    && (( 10#$phase_finished >= 10#$phase_started )); then
    phase_elapsed=$((10#$phase_finished - 10#$phase_started))
  fi
  printf 'LEAN_INSPECTOR_PHASE phase=%s status=completed clock=shell-seconds start_seconds=%s end_seconds=%s elapsed_seconds=%s exit=%s\n' \
    "$phase" "$phase_started" "$phase_finished" "$phase_elapsed" "$status" >&2 || true
  printf '%s\n' "$status" > "$LOG_DIR/$phase.exit.log"
  printf '%s\n' "$phase_elapsed" > "$LOG_DIR/$phase.seconds.log"
  if [[ "$status" != 0 ]]; then
    printf 'LEAN_INSPECTOR_FAILED phase=%s exit=%s\n' "$phase" "$status" >&2
    cat "$LOG_DIR/$phase.stdout.log" "$LOG_DIR/$phase.stderr.log" >&2
    return "$status"
  fi
}

# Validate required authored inputs before provisioning or consuming artifacts.
run_phase inputs python3 "$SCRIPT_DIR/../scripts/report/lean-report-selection.py" validate --repository "$REPOSITORY"
run_phase batch-size python3 "$SCRIPT_DIR/native.py" batch-size
if [[ -n "${STRATALINT_LEAN_PRODUCER_DLL:-}" ]]; then
  [[ "$STRATALINT_LEAN_PRODUCER_DLL" == /* && -f "$STRATALINT_LEAN_PRODUCER_DLL" ]] \
    || { echo 'inspect.sh: candidate Lean producer must be an existing absolute path' >&2; exit 2; }
fi
workspace=(-d "$REPOSITORY/tools/lean-inspector-reg")
require_lake() {
  LAKE="${LAKE_BIN:-$(command -v lake || true)}"
  if [[ -z "$LAKE" ]]; then
    # A seed can fail publication after resource planning. Obtain the normal
    # toolchain only when report extraction is required, including that miss.
    run_phase toolchain "$REPOSITORY/tools/scripts/workflow/install-lean-toolchain.sh" \
      "$REPOSITORY/lean-toolchain" --github-path "$STARTUP_LOG_DIR/toolchain-path"
    local toolchain_directory
    IFS= read -r toolchain_directory < "$STARTUP_LOG_DIR/toolchain-path"
    LAKE="$toolchain_directory/lake"
  fi
  [[ -n "$LAKE" && "$LAKE" == /* && -x "$LAKE" ]] \
    || { echo 'inspect.sh: an absolute executable lake path is required (LAKE_BIN)' >&2; return 2; }
  export LAKE_BIN="$LAKE"
}
open_logs() {
  mkdir -p "$(dirname "$OUTPUT")" "$FINAL_LOG_DIR"
  mv -f -- "$STARTUP_LOG_DIR"/* "$FINAL_LOG_DIR/"
  LOG_DIR="$FINAL_LOG_DIR"
  export STRATALINT_INSPECTOR_ACTIVITY="$LOG_DIR/native-work.jsonl"
  : > "$STRATALINT_INSPECTOR_ACTIVITY"
  export STRATALINT_INSPECTOR_PHASES="$LOG_DIR/native-phases.jsonl"
  : > "$STRATALINT_INSPECTOR_PHASES"
}
if [[ "$CACHE_MISS_POLICY" == fetch-or-fail ]]; then
  run_phase seed python3 -B "$SCRIPT_DIR/reuse.py" require-compatible --repository "$REPOSITORY" \
    --report "${STRATALINT_LEAN_REPORT_REUSE:-$OUTPUT}"
  cat "$LOG_DIR/seed.stdout.log"
fi
require_lake
run_phase capture python3 -B "$SCRIPT_DIR/reuse.py" capture --repository "$REPOSITORY" \
  --report "$OUTPUT" --snapshot "$STARTUP_LOG_DIR/entry-inputs.json"
# A failed new default/report run must not leave an apparent successful seal.
run_phase prepare python3 -B "$SCRIPT_DIR/reuse.py" prepare --repository "$REPOSITORY" --report "$OUTPUT"
export STRATALINT_LEAN_PRODUCER_DLL="${STRATALINT_LEAN_PRODUCER_DLL:-$REPOSITORY/tools/StrataLint.Lean/bin/Release/net10.0/StrataLint.Lean.dll}"
[[ -f "$STRATALINT_LEAN_PRODUCER_DLL" ]] || {
  echo "inspect.sh: missing prebuilt producer $STRATALINT_LEAN_PRODUCER_DLL; run dotnet build tools/StrataLint.Lean -c Release" >&2
  exit 2
}
open_logs
# Lake schedules report extraction and reuse from existing compiler artifacts.
REPORT_COMMAND=()
if [[ "$REGENERATE_REPORT_ARTIFACTS" == 1 ]]; then
  # The cache guard encloses cleanup and the native report facet.
  REPORT_COMMAND=(python3 -B "$SCRIPT_DIR/native.py" regenerate "$REPOSITORY")
fi
run_phase report "$REPOSITORY/tools/scripts/worktree/lean-cache-run.sh" --prebuilt ${REPORT_COMMAND[@]+"${REPORT_COMMAND[@]}"} "$LAKE" --log-level=error "${workspace[@]}" build :report
# Publication and seal share one canonical cache guard.
run_phase publish python3 -B "$SCRIPT_DIR/native.py" publish "$REPOSITORY" "$OUTPUT" \
  "$LOG_DIR/entry-inputs.json"
cat "$LOG_DIR/publish.stdout.log"
