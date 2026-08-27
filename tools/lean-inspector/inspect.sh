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
[[ -x "$CACHE_RUN" ]] || { echo "inspect.sh: cache writer is absent: $CACHE_RUN" >&2; exit 2; }

finish_inspector() {
  local rc=$?
  trap - EXIT HUP INT TERM
  set +e
  [[ -z "$MODULE_TABLE" ]] || rm -f -- "$MODULE_TABLE"
  [[ -z "$DELTA_PLAN" ]] || rm -f -- "$DELTA_PLAN"
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
  while IFS=$'\t' read -r module path; do
    if [[ -n "$selection_file" ]] \
      && ! grep -Fqx -- "$module" "$selection_file"; then
      continue
    fi
    append_module "$module" "$path"
  done < "$MODULE_TABLE"
  [[ "${#inspector_arguments[@]}" -gt 0 ]] || return 2
  run_phase inspect \
    "$CACHE_RUN" "$LAKE" env lean --run "$INSPECTOR" \
    --output "$SPOOL_REPORT" --material-spool "$MATERIAL_SPOOL" \
    "${inspector_arguments[@]}"
  run_phase compact python3 "$compactor" compact \
    "$SPOOL_REPORT" "$MATERIAL_SPOOL" "$output"
  rm -rf -- "$SPOOL_REPORT" "$MATERIAL_SPOOL"
  SPOOL_REPORT=""
  MATERIAL_SPOOL=""
}

DELTA_SCRIPT="$INSPECTOR_DIR/delta.py"
delta_available=1
[[ -r "$DELTA_SCRIPT" ]] || delta_available=0
current_input_address="${STRATALINT_REPORT_INPUT_ADDRESS:-}"
current_repository_sha256="${STRATALINT_REPORT_REPOSITORY_SHA256:-}"
current_producer_sha256="${STRATALINT_REPORT_PRODUCER_SHA256:-}"
current_resident_sha256="${STRATALINT_REPORT_RESIDENT_SHA256:-}"
current_config_sha256="${STRATALINT_REPORT_CONFIG_SHA256:-}"
if [[ ! "$current_input_address" =~ ^[0-9a-f]{64}$ \
   || ! "$current_repository_sha256" =~ ^[0-9a-f]{64}$ \
   || ! "$current_producer_sha256" =~ ^[0-9a-f]{64}$ \
   || ! "$current_resident_sha256" =~ ^[0-9a-f]{64}$ \
   || ! "$current_config_sha256" =~ ^[0-9a-f]{64}$ ]]; then
  input_address_output="$("$INPUT_HELPER" address --repository "$REPOSITORY" \
    --producer "$INSPECTOR_DIR/inspect.sh" --inspector "$INSPECTOR")" \
    || input_address_output=""
  current_sources_sha256=""
  read -r current_repository_sha256 current_resident_sha256 current_sources_sha256 current_config_sha256 \
    <<< "$input_address_output"
  current_producer_sha256="$current_resident_sha256"
  if [[ "$current_repository_sha256" =~ ^[0-9a-f]{64}$ \
     && "$current_producer_sha256" =~ ^[0-9a-f]{64}$ \
     && "$current_sources_sha256" =~ ^[0-9a-f]{64}$ \
     && "$current_config_sha256" =~ ^[0-9a-f]{64}$ ]]; then
    if command -v sha256sum >/dev/null 2>&1; then
      current_input_address="$(printf '%s\n' \
        'schema=stratalint-lean-report-input-v1' \
        "producer_sha256=$current_producer_sha256" \
        "repository_inspector_sha256=$current_resident_sha256" \
        "lean_sources_sha256=$current_sources_sha256" \
        "lean_config_sha256=$current_config_sha256" | sha256sum | awk '{print $1}')"
    else
      current_input_address="$(printf '%s\n' \
        'schema=stratalint-lean-report-input-v1' \
        "producer_sha256=$current_producer_sha256" \
        "repository_inspector_sha256=$current_resident_sha256" \
        "lean_sources_sha256=$current_sources_sha256" \
        "lean_config_sha256=$current_config_sha256" | shasum -a 256 | awk '{print $1}')"
    fi
  fi
fi

DELTA_PLAN="$(mktemp "${TMPDIR:-/tmp}/stratalint-report-delta-plan.XXXXXXXX")"
DELTA_SUBSET_OUTPUT="$(mktemp "${TMPDIR:-/tmp}/stratalint-report-delta-output.XXXXXXXX")"
delta_status="fallback"
delta_baseline=""
delta_recheck_count=0
delta_changed_count=0
delta_added_count=0
delta_removed_count=0

cache_root_trusted() {
  [[ -n "${STRATALINT_REPORT_CACHE_ROOT:-}" \
    && -d "$STRATALINT_REPORT_CACHE_ROOT" ]] || return 1
  local owner perm
  if owner="$(stat -f '%u' "$STRATALINT_REPORT_CACHE_ROOT" 2>/dev/null)" \
    && perm="$(stat -f '%Lp' "$STRATALINT_REPORT_CACHE_ROOT" 2>/dev/null)"; then
    :
  elif owner="$(stat -c '%u' "$STRATALINT_REPORT_CACHE_ROOT" 2>/dev/null)" \
    && perm="$(stat -c '%a' "$STRATALINT_REPORT_CACHE_ROOT" 2>/dev/null)"; then
    :
  else
    return 1
  fi
  [[ "$owner" == "$(id -u)" && "$perm" =~ ^[0-7]+$ ]] || return 1
  (( (8#$perm & 8#22) == 0 ))
}

if [[ "$delta_available" == "1" ]] \
  && cache_root_trusted \
  && [[ "$current_input_address" =~ ^[0-9a-f]{64}$ \
     && "$current_repository_sha256" =~ ^[0-9a-f]{64}$ \
     && "$current_producer_sha256" =~ ^[0-9a-f]{64}$ \
     && "$current_resident_sha256" =~ ^[0-9a-f]{64}$ \
     && "$current_config_sha256" =~ ^[0-9a-f]{64}$ ]]; then
  python3 "$DELTA_SCRIPT" plan \
    "$REPOSITORY" "$STRATALINT_REPORT_CACHE_ROOT" "$current_input_address" \
    "$current_producer_sha256" "$current_resident_sha256" "$current_config_sha256" \
    "$MODULE_TABLE" "$DELTA_PLAN" || true
  if [[ -s "$DELTA_PLAN" ]]; then
    delta_status="$(python3 - "$DELTA_PLAN" <<'PY'
import json, pathlib, sys
print(json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8")).get("status", "fallback"))
PY
)"
    if [[ "$delta_status" == "delta" || "$delta_status" == "reuse" ]]; then
      delta_baseline="$(python3 - "$DELTA_PLAN" <<'PY'
import json, pathlib, sys
print(json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8")).get("baseline", ""))
PY
)"
      delta_recheck_count="$(python3 - "$DELTA_PLAN" <<'PY'
import json, pathlib, sys
print(len(json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8")).get("recheck", [])))
PY
)"
      delta_changed_count="$(python3 - "$DELTA_PLAN" <<'PY'
import json, pathlib, sys
print(len(json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8")).get("changed", [])))
PY
)"
      delta_added_count="$(python3 - "$DELTA_PLAN" <<'PY'
import json, pathlib, sys
print(len(json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8")).get("added", [])))
PY
)"
      delta_removed_count="$(python3 - "$DELTA_PLAN" <<'PY'
import json, pathlib, sys
print(len(json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8")).get("removed", [])))
PY
)"
    else
      delta_status="fallback"
    fi
  fi
fi

printf 'LEAN_REPORT_DELTA_PLAN mode=%s changed=%s added=%s removed=%s recheck=%s\n' \
  "$delta_status" "$delta_changed_count" "$delta_added_count" \
  "$delta_removed_count" "$delta_recheck_count"

if [[ "$delta_status" == "delta" && "$delta_recheck_count" -gt 0 ]]; then
  selection_file="$(mktemp "${TMPDIR:-/tmp}/stratalint-report-delta-selection.XXXXXXXX")"
  python3 - "$DELTA_PLAN" "$selection_file" <<'PY'
import json, pathlib, sys
plan = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
pathlib.Path(sys.argv[2]).write_text("".join(name + "\n" for name in plan["recheck"]), encoding="utf-8")
PY
  if ! invoke_inspector "$DELTA_SUBSET_OUTPUT" "$selection_file"; then
    delta_status="full-fallback"
  fi
  rm -f -- "$selection_file"
elif [[ "$delta_status" != "reuse" && "$delta_status" != "delta" ]]; then
  delta_status="full-fallback"
fi

if [[ "$delta_status" == "delta" || "$delta_status" == "reuse" ]]; then
  if [[ "$delta_status" == "reuse" ]]; then
    cp "$delta_baseline" "$OUTPUT"
    cp "${delta_baseline}.materials.zip" "${OUTPUT}.materials.zip"
  elif ! python3 "$DELTA_SCRIPT" merge \
      "$DELTA_PLAN" "$DELTA_SUBSET_OUTPUT" "$OUTPUT"; then
    delta_status="full-fallback"
  fi
fi

if [[ "$delta_status" == "full-fallback" ]]; then
  rm -rf -- "$DELTA_SUBSET_OUTPUT" "${DELTA_SUBSET_OUTPUT}.materials.zip"
  invoke_inspector "$OUTPUT"
fi

printf 'LEAN_REPORT_DELTA mode=%s changed=%s added=%s removed=%s recheck=%s\n' \
  "$delta_status" "$delta_changed_count" "$delta_added_count" \
  "$delta_removed_count" "$delta_recheck_count"

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
