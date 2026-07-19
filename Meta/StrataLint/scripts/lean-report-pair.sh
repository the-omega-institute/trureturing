#!/usr/bin/env bash
set -euo pipefail

export LC_ALL=C

PRODUCER=""
LAKE_BIN=""
CANDIDATE_ROOT=""
CANDIDATE_OUTPUT=""
BASELINE_ROOT=""
BASELINE_OUTPUT=""
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
SUPERVISOR="$SCRIPT_DIR/report-supervisor.sh"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --producer) PRODUCER="$2"; shift 2 ;;
    --lake-bin) LAKE_BIN="$2"; shift 2 ;;
    --candidate-root) CANDIDATE_ROOT="$2"; shift 2 ;;
    --candidate-output) CANDIDATE_OUTPUT="$2"; shift 2 ;;
    --baseline-root) BASELINE_ROOT="$2"; shift 2 ;;
    --baseline-output) BASELINE_OUTPUT="$2"; shift 2 ;;
    *) echo "lean-report-pair: unknown argument '$1'" >&2; exit 2 ;;
  esac
done

[[ -n "$PRODUCER" && "$PRODUCER" == /* && -x "$PRODUCER" ]] \
  || { echo "lean-report-pair: --producer requires an absolute executable" >&2; exit 2; }
[[ -n "$LAKE_BIN" && "$LAKE_BIN" == /* && -x "$LAKE_BIN" ]] \
  || { echo "lean-report-pair: --lake-bin requires an absolute executable" >&2; exit 2; }
[[ -d "$CANDIDATE_ROOT" ]] \
  || { echo "lean-report-pair: candidate root is absent" >&2; exit 2; }
[[ -d "$BASELINE_ROOT" ]] \
  || { echo "lean-report-pair: baseline root is absent" >&2; exit 2; }
[[ -n "$CANDIDATE_OUTPUT" && "$CANDIDATE_OUTPUT" == /* ]] \
  || { echo "lean-report-pair: candidate output must be absolute" >&2; exit 2; }
[[ -n "$BASELINE_OUTPUT" && "$BASELINE_OUTPUT" == /* ]] \
  || { echo "lean-report-pair: baseline output must be absolute" >&2; exit 2; }
[[ -x "$SUPERVISOR" ]] \
  || { echo "lean-report-pair: report supervisor is absent" >&2; exit 2; }

PRODUCER="$(cd "$(dirname "$PRODUCER")" && pwd -P)/$(basename "$PRODUCER")"
CANDIDATE_ROOT="$(cd "$CANDIDATE_ROOT" && pwd -P)"
BASELINE_ROOT="$(cd "$BASELINE_ROOT" && pwd -P)"
INSPECTOR="$(dirname "$PRODUCER")/Inspector.lean"
[[ -f "$INSPECTOR" ]] \
  || { echo "lean-report-pair: producer Inspector.lean is absent" >&2; exit 2; }

TMP_ROOT="$(mktemp -d)"
cleanup() { rm -rf -- "$TMP_ROOT"; }
trap cleanup EXIT
trap 'exit 129' HUP
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

append_manifest_entry() {
  local manifest="$1"
  local root="$2"
  local relative="$3"
  local path="$root/$relative"
  [[ -f "$path" ]] \
    || { echo "lean-report-pair: input is absent: $path" >&2; return 2; }
  printf '%s  %s\n' "$(hash_file "$path")" "$relative" >> "$manifest"
}

fingerprint() {
  local root="$1"
  local side="$2"
  local producer_manifest="$TMP_ROOT/$side-producer.manifest"
  local resident_manifest="$TMP_ROOT/$side-resident-inspector.manifest"
  local sources_manifest="$TMP_ROOT/$side-sources.manifest"
  local sources_list="$TMP_ROOT/$side-sources.list"
  local config_manifest="$TMP_ROOT/$side-config.manifest"
  local preimage="$TMP_ROOT/$side-input.preimage"
  local resident_root="Meta/StrataLint/lean-inspector"

  : > "$producer_manifest"
  printf '%s  inspect.sh\n' "$(hash_file "$PRODUCER")" >> "$producer_manifest"
  printf '%s  Inspector.lean\n' "$(hash_file "$INSPECTOR")" >> "$producer_manifest"
  local producer_sha256
  producer_sha256="$(hash_file "$producer_manifest")"

  : > "$resident_manifest"
  if [[ -f "$root/$resident_root/inspect.sh" \
    && -f "$root/$resident_root/Inspector.lean" ]]; then
    append_manifest_entry "$resident_manifest" "$root" "$resident_root/inspect.sh"
    append_manifest_entry "$resident_manifest" "$root" "$resident_root/Inspector.lean"
  else
    printf '%s\n' "resident-inspector-absent" > "$resident_manifest"
  fi
  local resident_sha256
  resident_sha256="$(hash_file "$resident_manifest")"

  : > "$sources_manifest"
  append_manifest_entry "$sources_manifest" "$root" "Trureturing.lean"
  [[ -d "$root/D5" ]] \
    || { echo "lean-report-pair: managed Lean root is absent: $root/D5" >&2; return 2; }
  find "$root/D5" -type f -name '*.lean' -print | sort > "$sources_list"
  while IFS= read -r path; do
    append_manifest_entry "$sources_manifest" "$root" "${path#"$root/"}"
  done < "$sources_list"
  local sources_sha256
  sources_sha256="$(hash_file "$sources_manifest")"

  : > "$config_manifest"
  append_manifest_entry "$config_manifest" "$root" "lean-toolchain"
  append_manifest_entry "$config_manifest" "$root" "lake-manifest.json"
  local lakefile_count=0
  local lakefile
  for lakefile in lakefile.toml lakefile.lean; do
    if [[ -f "$root/$lakefile" ]]; then
      append_manifest_entry "$config_manifest" "$root" "$lakefile"
      lakefile_count=$((lakefile_count + 1))
    fi
  done
  [[ "$lakefile_count" -gt 0 ]] \
    || { echo "lean-report-pair: repository has no lakefile: $root" >&2; return 2; }
  local config_sha256
  config_sha256="$(hash_file "$config_manifest")"

  {
    printf '%s\n' "schema=stratalint-lean-report-input-v1"
    printf 'producer_sha256=%s\n' "$producer_sha256"
    printf 'repository_inspector_sha256=%s\n' "$resident_sha256"
    printf 'lean_sources_sha256=%s\n' "$sources_sha256"
    printf 'lean_config_sha256=%s\n' "$config_sha256"
  } > "$preimage"
  printf '%s %s %s %s %s\n' \
    "$(hash_file "$preimage")" \
    "$producer_sha256" \
    "$resident_sha256" \
    "$sources_sha256" \
    "$config_sha256"
}

verify_report() {
  local output="$1"
  [[ -s "$output" ]] \
    || { echo "lean-report-pair: producer left no report: $output" >&2; return 2; }
  [[ -f "${output}.sha256" ]] \
    || { echo "lean-report-pair: producer left no SHA sidecar: $output" >&2; return 2; }
  local declared=""
  local declared_name=""
  read -r declared declared_name < "${output}.sha256"
  local actual
  actual="$(hash_file "$output")"
  [[ "$declared" =~ ^[0-9a-f]{64}$ \
    && "$declared" == "$actual" \
    && "$declared_name" == "$(basename "$output")" \
    && "$(awk 'END {print NR}' "${output}.sha256")" == "1" ]] \
    || { echo "lean-report-pair: report SHA sidecar mismatch: $output" >&2; return 2; }
  LAST_REPORT_SHA256="$actual"
}

produce_report() {
  local side="$1"
  local root="$2"
  local output="$3"
  rm -f -- "$output" "${output}.sha256" "${output}.provenance.json"
  mkdir -p "$(dirname "$output")"
  "$SUPERVISOR" --role "lean-producer-$side" --lean-slot -- \
    env LAKE_BIN="$LAKE_BIN" "$PRODUCER" --repository "$root" --output "$output"
  verify_report "$output"
}

write_sidecar() {
  local output="$1"
  local sha256="$2"
  printf '%s  %s\n' "$sha256" "$(basename "$output")" > "${output}.sha256"
}

write_provenance() {
  local side="$1"
  local output="$2"
  local mode="$3"
  local source_side="$4"
  local input_address="$5"
  local producer_sha256="$6"
  local resident_sha256="$7"
  local sources_sha256="$8"
  local config_sha256="$9"
  local report_sha256="${10}"
  printf '{"schema":"stratalint-lean-report-provenance-v1","side":"%s","mode":"%s","source_side":"%s","input_address":"sha256:%s","producer_sha256":"%s","repository_inspector_sha256":"%s","lean_sources_sha256":"%s","lean_config_sha256":"%s","report_sha256":"%s"}\n' \
    "$side" "$mode" "$source_side" "$input_address" "$producer_sha256" \
    "$resident_sha256" "$sources_sha256" "$config_sha256" "$report_sha256" \
    > "${output}.provenance.json"
  printf 'LEAN_REPORT_PROVENANCE side=%s mode=%s source_side=%s input_address=sha256:%s report_sha256=%s attestation=%s\n' \
    "$side" "$mode" "$source_side" "$input_address" "$report_sha256" \
    "${output}.provenance.json"
}

read -r candidate_address candidate_producer candidate_resident candidate_sources candidate_config \
  <<< "$(fingerprint "$CANDIDATE_ROOT" candidate)"
read -r baseline_address baseline_producer baseline_resident baseline_sources baseline_config \
  <<< "$(fingerprint "$BASELINE_ROOT" baseline)"

printf 'LEAN_REPORT_INPUT side=candidate content_address=sha256:%s producer_sha256=%s repository_inspector_sha256=%s lean_sources_sha256=%s lean_config_sha256=%s\n' \
  "$candidate_address" "$candidate_producer" "$candidate_resident" "$candidate_sources" "$candidate_config"
printf 'LEAN_REPORT_INPUT side=baseline content_address=sha256:%s producer_sha256=%s repository_inspector_sha256=%s lean_sources_sha256=%s lean_config_sha256=%s\n' \
  "$baseline_address" "$baseline_producer" "$baseline_resident" "$baseline_sources" "$baseline_config"

produce_report candidate "$CANDIDATE_ROOT" "$CANDIDATE_OUTPUT"
candidate_report_sha256="$LAST_REPORT_SHA256"
write_provenance \
  candidate "$CANDIDATE_OUTPUT" produced candidate \
  "$candidate_address" "$candidate_producer" "$candidate_resident" \
  "$candidate_sources" "$candidate_config" "$candidate_report_sha256"

if [[ "$candidate_address" == "$baseline_address" ]]; then
  rm -f -- "$BASELINE_OUTPUT" "${BASELINE_OUTPUT}.sha256" "${BASELINE_OUTPUT}.provenance.json"
  rm -rf -- "${BASELINE_OUTPUT}.logs"
  mkdir -p "$(dirname "$BASELINE_OUTPUT")"
  cp "$CANDIDATE_OUTPUT" "$BASELINE_OUTPUT"
  verify_report_copy_sha256="$(hash_file "$BASELINE_OUTPUT")"
  [[ "$verify_report_copy_sha256" == "$candidate_report_sha256" ]] \
    || { echo "lean-report-pair: reused report copy changed bytes" >&2; exit 2; }
  write_sidecar "$BASELINE_OUTPUT" "$verify_report_copy_sha256"
  write_provenance \
    baseline "$BASELINE_OUTPUT" reused candidate \
    "$baseline_address" "$baseline_producer" "$baseline_resident" \
    "$baseline_sources" "$baseline_config" "$verify_report_copy_sha256"
else
  produce_report baseline "$BASELINE_ROOT" "$BASELINE_OUTPUT"
  baseline_report_sha256="$LAST_REPORT_SHA256"
  write_provenance \
    baseline "$BASELINE_OUTPUT" produced baseline \
    "$baseline_address" "$baseline_producer" "$baseline_resident" \
    "$baseline_sources" "$baseline_config" "$baseline_report_sha256"
fi
