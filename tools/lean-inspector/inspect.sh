#!/usr/bin/env bash
set -euo pipefail

export LC_ALL=C

REPOSITORY=""
OUTPUT=""
LOG_DIR=""
MODULE_TABLE=""
DELTA_PLAN=""
DELTA_SUBSET_OUTPUT=""
MATERIAL_SPOOL=""
SPOOL_REPORT=""
PREPARE_ONLY=0
PREPARATION=""
OWN_PREPARATION=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --prepare) PREPARE_ONLY=1; shift ;;
    --preparation)
      [[ $# -ge 2 ]] || { echo "inspect.sh: --preparation requires a value" >&2; exit 2; }
      PREPARATION="$2"; shift 2 ;;
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
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
INPUT_HELPER="$SCRIPT_DIR/../scripts/report/lean-report-input.sh"
[[ -x "$INPUT_HELPER" ]] || { echo "inspect.sh: module enumerator is absent: $INPUT_HELPER" >&2; exit 2; }
# Environment hints cannot bypass the candidate manifest or retain an older
# compatibility version. Validate before changing outputs or invoking Lake.
compatibility_token="$("$INPUT_HELPER" compatibility-token --repository "$REPOSITORY")" || exit 2
[[ "$compatibility_token" =~ ^[0-9a-f]{64}$ ]] \
  || { echo "inspect.sh: compatibility token is malformed" >&2; exit 2; }
PREPARATION_HELPER="$SCRIPT_DIR/preparation.py"
preparation_command=prepare
if [[ -n "${STRATALINT_LEAN_REPORT_PREPARATION:-}" ]]; then
  [[ -z "$PREPARATION" || "$PREPARATION" == "$STRATALINT_LEAN_REPORT_PREPARATION" ]] \
    || { echo 'inspect.sh: conflicting preparation directories' >&2; exit 2; }
  PREPARATION="$STRATALINT_LEAN_REPORT_PREPARATION"
  if [[ "$PREPARE_ONLY" == 0 ]]; then preparation_command=resume; fi
elif [[ -z "$PREPARATION" ]]; then
  [[ "$PREPARE_ONLY" == 0 ]] || { echo 'inspect.sh: --prepare requires --preparation' >&2; exit 2; }
  PREPARATION="$(mktemp -d "$REPOSITORY/.lean-report-preparation.XXXXXXXX")"
  OWN_PREPARATION=1
fi
if [[ "$PREPARE_ONLY" == 1 ]]; then
  exec python3 "$PREPARATION_HELPER" "$preparation_command" --repository "$REPOSITORY" --directory "$PREPARATION"
fi
DELTA_PLAN="$(mktemp "${TMPDIR:-/tmp}/stratalint-report-delta-plan.XXXXXXXX")"
cleanup_preparation() {
  rm -f -- "$DELTA_PLAN"
  if [[ "$OWN_PREPARATION" == 1 ]]; then rm -rf -- "$PREPARATION"; fi
}
trap cleanup_preparation EXIT
preparation_values="$(python3 "$PREPARATION_HELPER" "$preparation_command" \
  --repository "$REPOSITORY" --directory "$PREPARATION" --execution-plan "$DELTA_PLAN")" || exit 2
fields=()
while IFS= read -r value; do fields+=("$value"); done <<< "$preparation_values"
[[ "${#fields[@]}" == 10 ]] || { echo 'inspect.sh: preparation output is malformed' >&2; exit 2; }
runtime_sha256="${fields[0]}" cache_partition="${fields[1]}"
LAKE="${fields[2]}" LEAN="${fields[3]}"
export LAKE_BIN="$LAKE" LEAN_BIN="$LEAN"
delta_status="${fields[4]}" delta_baseline="${fields[5]}"
delta_recheck_count="${fields[6]}" delta_changed_count="${fields[7]}"
delta_added_count="${fields[8]}" delta_removed_count="${fields[9]}"
MODULE_TABLE="$PREPARATION/modules.tsv"

if [[ "$OUTPUT" != /* ]]; then OUTPUT="$REPOSITORY/$OUTPUT"; fi
if [[ -z "$LOG_DIR" ]]; then LOG_DIR="${OUTPUT}.logs"; fi
if [[ "$LOG_DIR" != /* ]]; then LOG_DIR="$REPOSITORY/$LOG_DIR"; fi
mkdir -p "$(dirname "$OUTPUT")" "$LOG_DIR"
rm -rf -- "$OUTPUT" "${OUTPUT}.sha256" "${OUTPUT}.materials" "${OUTPUT}.materials.zip" "${OUTPUT}.seed.json" "${OUTPUT}.execution.json"

source "$SCRIPT_DIR/../scripts/lib/resource-observation-lib.sh"
INSPECTOR="$SCRIPT_DIR/Inspector.lean"
[[ -f "$INSPECTOR" ]] || { echo "inspect.sh: Lean producer is absent: $INSPECTOR" >&2; exit 2; }

CACHE_RUN="$REPOSITORY/tools/scripts/worktree/lean-cache-run.sh"
[[ -x "$CACHE_RUN" ]] || { echo "inspect.sh: cache reader is absent: $CACHE_RUN" >&2; exit 2; }

finish_inspector() {
  local rc=$?
  trap - EXIT HUP INT TERM
  set +e
  cleanup_preparation
  [[ -z "$DELTA_SUBSET_OUTPUT" ]] || rm -f -- "$DELTA_SUBSET_OUTPUT"
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

  printf 'LEAN_INSPECTOR_PHASE phase=%s status=started\n' "$phase"
  set +e
  (cd "$REPOSITORY" && "$@") > "$stdout_log" 2> "$stderr_log"
  local status=$?
  set -e
  printf '%s\n' "$status" > "$exit_log"
  printf 'LEAN_INSPECTOR_PHASE phase=%s status=finished exit=%s\n' "$phase" "$status"
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

# Build only when the validated report plan requires inspection. A partial
# recheck asks Lake for the selected module targets and their dependencies.
lake_build_done=0
lake_build_executed=0
ensure_lake_build() {
  if [[ "$lake_build_done" == "0" ]]; then
    local -a lake_build_args=(build)
    if [[ "${#build_targets[@]}" -gt 0 && "${#build_targets[@]}" -lt "$module_count" ]]; then
      lake_build_args+=("${build_targets[@]}")
    fi
    run_phase build "$CACHE_RUN" "$LAKE" "${lake_build_args[@]}" || return $?
    lake_build_done=1
    lake_build_executed=1
  fi
}

INSPECTOR_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"

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
  local selection_file="${2:-}"
  local compactor="$INSPECTOR_DIR/materials.py"
  [[ -r "$compactor" ]] || { echo "inspect.sh: material compactor is absent: $compactor" >&2; return 2; }
  SPOOL_REPORT="${output}.spool.json"
  MATERIAL_SPOOL="${output}.material-spool"
  rm -rf -- "$SPOOL_REPORT" "$MATERIAL_SPOOL" "${output}.materials" "${output}.materials.zip"
  mkdir -p "$MATERIAL_SPOOL"
  inspector_arguments=()
  build_targets=()
  module_count=0
  while IFS=$'\t' read -r module path; do
    ((module_count+=1))
    if [[ -n "$selection_file" ]] \
      && ! grep -Fqx -- "$module" "$selection_file"; then
      continue
    fi
    append_module "$module" "$path" || return $?
    build_targets+=("+$module")
  done < "$MODULE_TABLE"
  [[ "${#inspector_arguments[@]}" -gt 0 ]] || return 2
  if [[ -n "${STRATALINT_LEAN_PRODUCER_DLL:-}" ]]; then
    [[ "$STRATALINT_LEAN_PRODUCER_DLL" == /* && -f "$STRATALINT_LEAN_PRODUCER_DLL" ]] \
      || { echo "inspect.sh: candidate producer is absent: $STRATALINT_LEAN_PRODUCER_DLL" >&2; return 2; }
    run_phase utility-input dotnet "$STRATALINT_LEAN_PRODUCER_DLL" lean-utility-input || return $?
  else
    run_phase utility-input-build dotnet build \
      "$INSPECTOR_DIR/../StrataLint.Lean/StrataLint.Lean.csproj" --configuration Release --nologo --verbosity quiet || return $?
    run_phase utility-input dotnet run \
      --project "$INSPECTOR_DIR/../StrataLint.Lean/StrataLint.Lean.csproj" \
      --configuration Release --no-build --no-restore --no-launch-profile -- lean-utility-input || return $?
  fi
  ensure_lake_build || return $?
  run_phase inspect \
    "$CACHE_RUN" "$LAKE" env "$LEAN" --run "$INSPECTOR" \
    --output "$SPOOL_REPORT" --material-spool "$MATERIAL_SPOOL" \
    --utility-input "$LOG_DIR/utility-input.stdout.log" \
    "${inspector_arguments[@]}" || return $?
  run_phase compact python3 "$compactor" compact \
    "$SPOOL_REPORT" "$MATERIAL_SPOOL" "$output" || return $?
  rm -rf -- "$SPOOL_REPORT" "$MATERIAL_SPOOL"
  SPOOL_REPORT=""
  MATERIAL_SPOOL=""
}

DELTA_SCRIPT="$INSPECTOR_DIR/delta.py"
DELTA_SUBSET_OUTPUT="$(mktemp "${TMPDIR:-/tmp}/stratalint-report-delta-output.XXXXXXXX")"

printf 'LEAN_REPORT_DELTA_PLAN mode=%s changed=%s added=%s removed=%s recheck=%s\n' \
  "$delta_status" "$delta_changed_count" "$delta_added_count" \
  "$delta_removed_count" "$delta_recheck_count" | tee "$LOG_DIR/delta.log"

if [[ "$delta_status" == "delta" && "$delta_recheck_count" -gt 0 ]]; then
  selection_file="$(mktemp "${TMPDIR:-/tmp}/stratalint-report-delta-selection.XXXXXXXX")"
  python3 - "$DELTA_PLAN" "$selection_file" <<'PY'
import json, pathlib, sys
plan = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
pathlib.Path(sys.argv[2]).write_text("".join(name + "\n" for name in plan["recheck"]), encoding="utf-8")
PY
  # A genuine Lean/producer failure is blocking. Only unusable seed data falls
  # back to full production; failure cannot be replaced with an old report.
  invoke_inspector "$DELTA_SUBSET_OUTPUT" "$selection_file"
  rm -f -- "$selection_file"
elif [[ "$delta_status" != "reuse" && "$delta_status" != "delta" ]]; then
  delta_status="full-fallback"
fi

if [[ "$delta_status" == "delta" || "$delta_status" == "reuse" ]]; then
  if ! run_phase delta-merge python3 "$DELTA_SCRIPT" merge \
      "$DELTA_PLAN" "$DELTA_SUBSET_OUTPUT" "$OUTPUT"; then
    delta_status="full-fallback"
  fi
fi

if [[ "$delta_status" == "full-fallback" ]]; then
  rm -rf -- "$DELTA_SUBSET_OUTPUT" "${DELTA_SUBSET_OUTPUT}.materials.zip"
  # A failed seed merge can widen an already-built partial selection.
  lake_build_done=0
  invoke_inspector "$OUTPUT"
  delta_recheck_count="$(wc -l < "$MODULE_TABLE" | tr -d ' ')"
fi

printf 'LEAN_REPORT_DELTA mode=%s changed=%s added=%s removed=%s recheck=%s\n' \
  "$delta_status" "$delta_changed_count" "$delta_added_count" \
  "$delta_removed_count" "$delta_recheck_count" | tee -a "$LOG_DIR/delta.log"

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
python3 - "${OUTPUT}.seed.json" "$runtime_sha256" <<'PY'
import json, pathlib, sys
pathlib.Path(sys.argv[1]).write_text(json.dumps({"runtime_sha256": sys.argv[2]}) + "\n")
PY
python3 - "${OUTPUT}.execution.json" "$lake_build_executed" <<'PYEXEC'
import json, pathlib, sys
pathlib.Path(sys.argv[1]).write_text(json.dumps({"lean_build_succeeded": sys.argv[2] == "1"}) + "\n")
PYEXEC
printf 'RAW_LEAN_REPORT file=%s content_address=sha256:%s\n' "$OUTPUT" "$report_sha256"
