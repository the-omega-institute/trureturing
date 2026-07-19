#!/usr/bin/env bash
set -euo pipefail

export LC_ALL=C

COMMAND="${1:-}"
if [[ -n "$COMMAND" ]]; then shift; fi
REPOSITORY=""
REPORT=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --repository) REPOSITORY="$2"; shift 2 ;;
    --report) REPORT="$2"; shift 2 ;;
    *) echo "lean-report-input: unknown argument '$1'" >&2; exit 2 ;;
  esac
done

[[ "$COMMAND" == "address" || "$COMMAND" == "write-sidecar" || "$COMMAND" == "verify" ]] \
  || { echo "usage: lean-report-input.sh address|write-sidecar|verify --repository DIR [--report FILE]" >&2; exit 2; }
[[ -n "$REPOSITORY" && "$REPOSITORY" == /* && -d "$REPOSITORY" ]] \
  || { echo "lean-report-input: --repository requires an absolute directory" >&2; exit 2; }
REPOSITORY="$(cd "$REPOSITORY" && pwd -P)"
if [[ "$COMMAND" != "address" ]]; then
  [[ -n "$REPORT" && "$REPORT" == /* && -s "$REPORT" ]] \
    || { echo "lean-report-input: raw Lean report is missing; run make lean-report first" >&2; exit 2; }
fi

TMP_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/stratalint-report-input.XXXXXXXX")"
cleanup() { rm -rf -- "$TMP_ROOT"; }
trap cleanup EXIT

hash_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  elif command -v openssl >/dev/null 2>&1; then
    openssl dgst -sha256 "$1" | awk '{print $NF}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

append_manifest_entry() {
  local manifest="$1"
  local relative="$2"
  local path="$REPOSITORY/$relative"
  [[ -f "$path" ]] \
    || { echo "lean-report-input: repository input is absent: $path" >&2; return 2; }
  printf '%s  %s\n' "$(hash_file "$path")" "$relative" >> "$manifest"
}

repository_address() {
  local resident_manifest="$TMP_ROOT/resident-inspector.manifest"
  local sources_manifest="$TMP_ROOT/sources.manifest"
  local sources_list="$TMP_ROOT/sources.list"
  local config_manifest="$TMP_ROOT/config.manifest"
  local preimage="$TMP_ROOT/repository-input.preimage"
  local resident_root="Meta/StrataLint/lean-inspector"
  local resident_sha256 sources_sha256 config_sha256 lakefile_count=0 lakefile

  : > "$resident_manifest"
  append_manifest_entry "$resident_manifest" "$resident_root/inspect.sh"
  append_manifest_entry "$resident_manifest" "$resident_root/Inspector.lean"
  resident_sha256="$(hash_file "$resident_manifest")"

  : > "$sources_manifest"
  append_manifest_entry "$sources_manifest" "Trureturing.lean"
  [[ -d "$REPOSITORY/D5" ]] \
    || { echo "lean-report-input: managed Lean root is absent: $REPOSITORY/D5" >&2; return 2; }
  find "$REPOSITORY/D5" -type f -name '*.lean' -print | sort > "$sources_list"
  while IFS= read -r path; do
    append_manifest_entry "$sources_manifest" "${path#"$REPOSITORY/"}"
  done < "$sources_list"
  sources_sha256="$(hash_file "$sources_manifest")"

  : > "$config_manifest"
  append_manifest_entry "$config_manifest" "lean-toolchain"
  append_manifest_entry "$config_manifest" "lake-manifest.json"
  for lakefile in lakefile.toml lakefile.lean; do
    if [[ -f "$REPOSITORY/$lakefile" ]]; then
      append_manifest_entry "$config_manifest" "$lakefile"
      lakefile_count=$((lakefile_count + 1))
    fi
  done
  [[ "$lakefile_count" -gt 0 ]] \
    || { echo "lean-report-input: repository has no lakefile" >&2; return 2; }
  config_sha256="$(hash_file "$config_manifest")"

  {
    printf '%s\n' "schema=stratalint-lean-report-repository-input-v1"
    printf 'repository_inspector_sha256=%s\n' "$resident_sha256"
    printf 'lean_sources_sha256=%s\n' "$sources_sha256"
    printf 'lean_config_sha256=%s\n' "$config_sha256"
  } > "$preimage"
  printf '%s %s %s %s\n' \
    "$(hash_file "$preimage")" "$resident_sha256" "$sources_sha256" "$config_sha256"
}

verify_report_sha() {
  local declared="" declared_name="" actual
  [[ -f "${REPORT}.sha256" ]] \
    || { echo "lean-report-input: report SHA is missing; run make lean-report first" >&2; return 2; }
  read -r declared declared_name < "${REPORT}.sha256" || true
  actual="$(hash_file "$REPORT")"
  [[ "$declared" =~ ^[0-9a-f]{64}$ \
    && "$declared" == "$actual" \
    && "$declared_name" == "$(basename "$REPORT")" \
    && "$(awk 'END {print NR}' "${REPORT}.sha256")" == "1" ]] \
    || { echo "lean-report-input: raw Lean report SHA is stale; run make lean-report first" >&2; return 2; }
}

case "$COMMAND" in
  address)
    repository_address
    ;;
  write-sidecar)
    verify_report_sha
    read -r address _ <<< "$(repository_address)"
    printf 'sha256:%s  %s.repository-input\n' "$address" "$(basename "$REPORT")" \
      > "${REPORT}.repository.sha256"
    ;;
  verify)
    verify_report_sha
    [[ -s "${REPORT}.provenance.json" ]] \
      || { echo "lean-report-input: report provenance is missing; run make lean-report first" >&2; exit 2; }
    [[ -f "${REPORT}.repository.sha256" ]] \
      || { echo "lean-report-input: repository input address is missing; run make lean-report first" >&2; exit 2; }
    declared=""
    declared_name=""
    read -r declared declared_name < "${REPORT}.repository.sha256" || true
    read -r address _ <<< "$(repository_address)"
    [[ "$declared" == "sha256:$address" \
      && "$declared_name" == "$(basename "$REPORT").repository-input" \
      && "$(awk 'END {print NR}' "${REPORT}.repository.sha256")" == "1" ]] \
      || { echo "lean-report-input: raw Lean report is stale for current repository inputs; run make lean-report first" >&2; exit 2; }
    ;;
esac
