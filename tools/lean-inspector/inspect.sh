#!/usr/bin/env bash
set -euo pipefail

export LC_ALL=C

REPOSITORY=""
OUTPUT=""
SOURCE_BASE="${STRATALINT_SOURCE_BASE:-}"
LOG_DIR=""
MODULE_TABLE=""
MATERIAL_SPOOL=""
SPOOL_REPORT=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --base) SOURCE_BASE="$2"; shift 2 ;;
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
rm -rf -- "$OUTPUT" "${OUTPUT}.sha256" "${OUTPUT}.materials" "${OUTPUT}.materials.zip"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
source "$SCRIPT_DIR/../scripts/lib/resource-observation-lib.sh"
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
[[ -x "$CACHE_RUN" ]] || { echo "inspect.sh: cache reader is absent: $CACHE_RUN" >&2; exit 2; }

finish_inspector() {
  local rc=$?
  trap - EXIT HUP INT TERM
  set +e
  [[ -z "$MODULE_TABLE" ]] || rm -f -- "$MODULE_TABLE"
  [[ -z "$MATERIAL_SPOOL" ]] || rm -rf -- "$MATERIAL_SPOOL"
  [[ -z "$SPOOL_REPORT" ]] || rm -f -- "$SPOOL_REPORT"
  resource_observe lean-inspector-finish "$REPOSITORY" || true
  exit "$rc"
}
trap finish_inspector EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
resource_observe lean-inspector-start "$REPOSITORY" || true

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

  set +e
  (cd "$REPOSITORY" && "$@") > "$stdout_log" 2> "$stderr_log"
  local status=$?
  set -e
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

# Both Lake phases use the canonical reader and private build outputs.
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

invoke_inspector() {
  local output="$1"
  local compactor="$INSPECTOR_DIR/materials.py"
  [[ -r "$compactor" ]] || { echo "inspect.sh: material compactor is absent: $compactor" >&2; return 2; }
  SPOOL_REPORT="${output}.spool.json"
  MATERIAL_SPOOL="${output}.material-spool"
  rm -rf -- "$SPOOL_REPORT" "$MATERIAL_SPOOL" "${output}.materials" "${output}.materials.zip"
  mkdir -p "$MATERIAL_SPOOL"
  inspector_arguments=()
  while IFS=$'\t' read -r module path; do
    append_module "$module" "$path"
  done < "$MODULE_TABLE"
  [[ "${#inspector_arguments[@]}" -gt 0 ]] || return 2
  run_phase utility-input-build dotnet build \
    "$INSPECTOR_DIR/../StrataLint.Cli/StrataLint.Cli.csproj" --configuration Release --nologo --verbosity quiet
  run_phase utility-input dotnet run \
    --project "$INSPECTOR_DIR/../StrataLint.Cli/StrataLint.Cli.csproj" \
    --configuration Release --no-build --no-restore --no-launch-profile -- lean-utility-input
  run_phase inspect \
    "$CACHE_RUN" "$LAKE" env lean --run "$INSPECTOR" \
    --output "$SPOOL_REPORT" --material-spool "$MATERIAL_SPOOL" \
    --utility-input "$LOG_DIR/utility-input.stdout.log" \
    "${inspector_arguments[@]}"
  run_phase compact python3 "$compactor" compact \
    "$SPOOL_REPORT" "$MATERIAL_SPOOL" "$output"
  rm -rf -- "$SPOOL_REPORT" "$MATERIAL_SPOOL"
  SPOOL_REPORT=""
  MATERIAL_SPOOL=""
}

# Validate the declared producer closure for direct inspector callers as well.
input_address_output="$("$INPUT_HELPER" address --repository "$REPOSITORY" \
  --producer "$INSPECTOR_DIR/inspect.sh" --inspector "$INSPECTOR")" \
  || { echo "inspect.sh: repository input address is unavailable" >&2; exit 2; }
address_pattern='^([0-9a-f]{64} ){3}[0-9a-f]{64}$'
[[ "$input_address_output" =~ $address_pattern ]] \
  || { echo "inspect.sh: repository input address is malformed" >&2; exit 2; }

invoke_inspector "$OUTPUT"

[[ -s "$OUTPUT" ]] || { echo "inspect.sh: producer left no report at $OUTPUT" >&2; exit 2; }
[[ -f "${OUTPUT}.materials.zip" ]] \
  || { echo "inspect.sh: producer left no material archive at ${OUTPUT}.materials.zip" >&2; exit 2; }
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
[[ "$serialize_rc" -eq 0 ]] || exit "$serialize_rc"
printf 'RAW_LEAN_REPORT file=%s content_address=sha256:%s\n' "$OUTPUT" "$report_sha256"

SOURCE_ARGS=()
if [[ -n "$SOURCE_BASE" || ( -z "${STRATALINT_PUSH_BEFORE:-}" && -z "${STRATALINT_PUSH_HEAD:-}" ) ]]; then
  SOURCE_ARGS=(--base "${SOURCE_BASE:-HEAD}")
fi
run_phase source-context "$BASH" "$REPOSITORY/tools/lean-inspector/source-context.sh" prepare \
  --repository "$REPOSITORY" --report "$OUTPUT" ${SOURCE_ARGS[@]+"${SOURCE_ARGS[@]}"} --lake "$LAKE"
