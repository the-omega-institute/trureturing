#!/usr/bin/env bash
set -euo pipefail

export LC_ALL=C

REPOSITORY=""
OUTPUT=""
LOG_DIR=""
MODULE_TABLE=""
PERF_TMP=""
PERF_EVENT_SPOOL=""
PERF_RUN_ID=""
PERF_BASE="unknown"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --repository)
      [[ $# -ge 2 ]] || { echo "inspect.sh: --repository requires a value" >&2; exit 2; }
      REPOSITORY="$2"
      shift 2
      ;;
    --output)
      [[ $# -ge 2 ]] || { echo "inspect.sh: --output requires a value" >&2; exit 2; }
      OUTPUT="$2"
      shift 2
      ;;
    --log-dir)
      [[ $# -ge 2 ]] || { echo "inspect.sh: --log-dir requires a value" >&2; exit 2; }
      LOG_DIR="$2"
      shift 2
      ;;
    *)
      echo "inspect.sh: unknown argument '$1'" >&2
      exit 2
      ;;
  esac
done

[[ -n "$REPOSITORY" ]] || { echo "inspect.sh: --repository ROOT is required" >&2; exit 2; }
[[ -n "$OUTPUT" ]] || { echo "inspect.sh: --output FILE is required" >&2; exit 2; }
[[ -d "$REPOSITORY" ]] || { echo "inspect.sh: repository '$REPOSITORY' is absent" >&2; exit 2; }

REPOSITORY="$(cd "$REPOSITORY" && pwd -P)"
if [[ "$OUTPUT" != /* ]]; then OUTPUT="$REPOSITORY/$OUTPUT"; fi
if [[ -z "$LOG_DIR" ]]; then LOG_DIR="${OUTPUT}.logs"; fi
if [[ "$LOG_DIR" != /* ]]; then LOG_DIR="$REPOSITORY/$LOG_DIR"; fi
mkdir -p "$(dirname "$OUTPUT")" "$LOG_DIR"
rm -f "$OUTPUT" "${OUTPUT}.sha256"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
INSPECTOR="$SCRIPT_DIR/Inspector.lean"
[[ -f "$INSPECTOR" ]] || { echo "inspect.sh: Lean producer is absent: $INSPECTOR" >&2; exit 2; }

LAKE="${LAKE_BIN:-}"
if [[ -z "$LAKE" && -x "$HOME/.elan/bin/lake" ]]; then
  LAKE="$HOME/.elan/bin/lake"
fi
if [[ -z "$LAKE" ]]; then
  LAKE="$(command -v lake || true)"
fi
[[ -n "$LAKE" && "$LAKE" == /* && -x "$LAKE" ]] \
  || { echo "inspect.sh: an absolute executable lake path is required (set LAKE_BIN)" >&2; exit 2; }
CACHE_RUN="$REPOSITORY/tools/scripts/worktree/lean-cache-run.sh"
[[ -x "$CACHE_RUN" ]] || { echo "inspect.sh: cache writer is absent: $CACHE_RUN" >&2; exit 2; }

# Segment timings are a side channel.  The producer remains usable in the small
# script fixtures that intentionally omit the performance library, and any ledger
# failure is non-fatal to report production.
PERF_LIB="$SCRIPT_DIR/../scripts/lib/perf-event-lib.sh"
if [[ "${STRATALINT_PERF_SEGMENTS:-0}" == "1" && -r "$PERF_LIB" ]]; then
  source "$PERF_LIB"
  PERF_TMP="$(perf_make_spool_dir "$REPOSITORY" stratalint-lean-report-perf 2>/dev/null || true)"
  if [[ -n "$PERF_TMP" ]]; then
    PERF_EVENT_SPOOL="$PERF_TMP/events.jsonl"
    : > "$PERF_EVENT_SPOOL" || PERF_EVENT_SPOOL=""
  fi
  PERF_BASE_REF="${STRATALINT_PERF_BASE:-origin/dev}"
  PERF_BASE="$(git -C "$REPOSITORY" rev-parse --verify "${PERF_BASE_REF}^{commit}" 2>/dev/null || printf unknown)"
  [[ "$PERF_BASE" =~ ^[0-9a-fA-F]{40}([0-9a-fA-F]{24})?$ ]] || PERF_BASE="unknown"
  PERF_RUN_ID="${STRATALINT_PERF_RUN_ID:-report-$(date +%s)-$$}"
fi

finish_inspector() {
  local rc=$?
  trap - EXIT HUP INT TERM
  set +e
  if [[ -n "$PERF_EVENT_SPOOL" ]]; then
    perf_flush_events "$REPOSITORY" "$PERF_EVENT_SPOOL" lean-producer >/dev/null 2>&1 || true
  fi
  [[ -z "$PERF_TMP" ]] || rm -rf -- "$PERF_TMP"
  [[ -z "$MODULE_TABLE" ]] || rm -f -- "$MODULE_TABLE"
  exit "$rc"
}
trap finish_inspector EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

hash_file() {
  local file="$1"
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$file" | awk '{print $1}'
  elif command -v openssl >/dev/null 2>&1; then
    openssl dgst -sha256 "$file" | awk '{print $NF}'
  else
    shasum -a 256 "$file" | awk '{print $1}'
  fi
}

run_phase() {
  local phase="$1"
  shift
  local stdout_log="$LOG_DIR/${phase}.stdout.log"
  local stderr_log="$LOG_DIR/${phase}.stderr.log"
  local command_log="$LOG_DIR/${phase}.command.log"
  local exit_log="$LOG_DIR/${phase}.exit.log"

  {
    printf 'cwd=%q\n' "$REPOSITORY"
    printf 'argv='
    printf ' %q' "$@"
    printf '\n'
  } > "$command_log"

  local started finished elapsed phase_status
  started="$(date +%s)"
  set +e
  (cd "$REPOSITORY" && "$@") > "$stdout_log" 2> "$stderr_log"
  local status=$?
  set -e
  finished="$(date +%s)"
  elapsed=$((finished - started))
  (( elapsed >= 0 )) || elapsed=0
  phase_status=passed
  [[ "$status" -eq 0 ]] || phase_status=failed
  if [[ -n "$PERF_EVENT_SPOOL" ]]; then
    perf_capture_event \
      "$PERF_EVENT_SPOOL" "$REPOSITORY" "$PERF_RUN_ID" report "$PERF_BASE" \
      "$phase" "$phase_status" "$elapsed" || true
  fi
  printf '%s\n' "$status" > "$exit_log"
  if [[ "$status" -ne 0 ]]; then
    printf 'LEAN_INSPECTOR_FAILED phase=%s exit=%s\n' "$phase" "$status" >&2
    printf '%s\n' '--- command ---' >&2
    cat "$command_log" >&2
    printf '%s\n' '--- stdout ---' >&2
    cat "$stdout_log" >&2
    printf '%s\n' '--- stderr ---' >&2
    cat "$stderr_log" >&2
    printf '%s\n' '--- exit ---' >&2
    cat "$exit_log" >&2
    return "$status"
  fi
}

# The cache writer converges the pinned mathlib cache before starting either Lake phase.
run_phase build "$CACHE_RUN" "$LAKE" build

INSPECTOR_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
INPUT_HELPER="$INSPECTOR_DIR/../scripts/report/lean-report-input.sh"
[[ -x "$INPUT_HELPER" ]] || { echo "inspect.sh: module enumerator is absent: $INPUT_HELPER" >&2; exit 2; }
MODULE_TABLE="$(mktemp "${TMPDIR:-/tmp}/stratalint-modules.XXXXXXXX")"
"$INPUT_HELPER" modules --repository "$REPOSITORY" > "$MODULE_TABLE"

inspector_arguments=()
append_module() {
  local module="$1" path="$2"
  [[ -f "$REPOSITORY/$path" ]] || { echo "inspect.sh: managed module is absent: $path" >&2; exit 2; }
  inspector_arguments+=(
    "$module"
    "$path"
    "sha256:$(hash_file "$REPOSITORY/$path")"
  )
}
while IFS=$'\t' read -r module path; do append_module "$module" "$path"; done < "$MODULE_TABLE"
[[ "${#inspector_arguments[@]}" -gt 0 ]] || { echo "inspect.sh: module selection is empty" >&2; exit 2; }

run_phase inspect \
  "$CACHE_RUN" "$LAKE" env lean --run "$INSPECTOR" --output "$OUTPUT" \
  "${inspector_arguments[@]}"

[[ -s "$OUTPUT" ]] || { echo "inspect.sh: producer left no report at $OUTPUT" >&2; exit 2; }
serialize_started="$(date +%s)"
serialize_rc=0
report_sha256=""
set +e
report_sha256="$(hash_file "$OUTPUT")"
serialize_rc=$?
if [[ "$serialize_rc" -eq 0 ]]; then
  printf '%s  %s\n' "$report_sha256" "$(basename "$OUTPUT")" > "${OUTPUT}.sha256"
  serialize_rc=$?
fi
set -e
serialize_finished="$(date +%s)"
serialize_elapsed=$((serialize_finished - serialize_started))
(( serialize_elapsed >= 0 )) || serialize_elapsed=0
serialize_status=passed
[[ "$serialize_rc" -eq 0 ]] || serialize_status=failed
if [[ -n "$PERF_EVENT_SPOOL" ]]; then
  perf_capture_event \
    "$PERF_EVENT_SPOOL" "$REPOSITORY" "$PERF_RUN_ID" report "$PERF_BASE" \
    serialize "$serialize_status" "$serialize_elapsed" || true
fi
[[ "$serialize_rc" -eq 0 ]] || exit "$serialize_rc"
printf 'RAW_LEAN_REPORT file=%s content_address=sha256:%s\n' "$OUTPUT" "$report_sha256"
