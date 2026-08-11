#!/usr/bin/env bash
set -euo pipefail

export LC_ALL=C

COMMAND="${1:-}"
if [[ -n "$COMMAND" ]]; then shift; fi
REPOSITORY=""
REPORT=""
MANIFEST=""
PRODUCER_OVERRIDE=""
INSPECTOR_OVERRIDE=""
ADDRESS_SIDE="candidate"
while [[ $# -gt 0 ]]; do
  case "$1" in
    --repository) REPOSITORY="$2"; shift 2 ;;
    --report) REPORT="$2"; shift 2 ;;
    --manifest) MANIFEST="$2"; shift 2 ;;
    --baseline) ADDRESS_SIDE="baseline"; shift ;;
    --producer) PRODUCER_OVERRIDE="$2"; shift 2 ;;
    --inspector) INSPECTOR_OVERRIDE="$2"; shift 2 ;;
    *) echo "lean-report-input: unknown argument '$1'" >&2; exit 2 ;;
  esac
done

[[ "$COMMAND" == "address" || "$COMMAND" == "verify" || "$COMMAND" == "modules" || "$COMMAND" == "manifest" || "$COMMAND" == "verify-manifest" ]] \
  || { echo "usage: lean-report-input.sh address|verify|modules|manifest|verify-manifest --repository DIR [--report FILE] [--manifest FILE]" >&2; exit 2; }
[[ -n "$REPOSITORY" && "$REPOSITORY" == /* && -d "$REPOSITORY" ]] \
  || { echo "lean-report-input: --repository requires an absolute directory" >&2; exit 2; }
[[ -z "$PRODUCER_OVERRIDE" || ( "$PRODUCER_OVERRIDE" == /* && -f "$PRODUCER_OVERRIDE" ) ]] \
  || { echo "lean-report-input: --producer requires an absolute file" >&2; exit 2; }
[[ -z "$INSPECTOR_OVERRIDE" || ( "$INSPECTOR_OVERRIDE" == /* && -f "$INSPECTOR_OVERRIDE" ) ]] \
  || { echo "lean-report-input: --inspector requires an absolute file" >&2; exit 2; }
REPOSITORY="$(cd "$REPOSITORY" && pwd -P)"
if [[ "$COMMAND" == "verify" || "$COMMAND" == "verify-manifest" ]]; then
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

append_producer_manifest_entry() {
  local manifest="$1"
  local relative="$2"
  local path="$REPOSITORY/$relative"
  if [[ "$relative" == "Meta/StrataLint/lean-inspector/inspect.sh" && -n "$PRODUCER_OVERRIDE" ]]; then
    path="$PRODUCER_OVERRIDE"
  elif [[ "$relative" == "Meta/StrataLint/lean-inspector/Inspector.lean" && -n "$INSPECTOR_OVERRIDE" ]]; then
    path="$INSPECTOR_OVERRIDE"
  fi
  [[ -f "$path" ]] \
    || { echo "lean-report-input: repository input is absent: $path" >&2; return 2; }
  printf '%s  %s\n' "$(hash_file "$path")" "$relative" >> "$manifest"
}

producer_paths() {
  local directory relative
  for directory in \
    Meta/StrataLint/StrataLint.Engine \
    Meta/StrataLint/StrataLint.Cli \
    Meta/StrataLint/StrataLint.Scribe; do
    if [[ -d "$REPOSITORY/$directory" ]]; then
      find "$REPOSITORY/$directory" -type f -name '*.cs' \
        ! -path '*/bin/*' ! -path '*/obj/*' -print
    fi
  done | sed "s#^$REPOSITORY/##"
  for relative in \
    Meta/StrataLint/lean-inspector/inspect.sh \
    Meta/StrataLint/lean-inspector/Inspector.lean \
    Meta/StrataLint/scripts/report/lean-report-input.sh \
    Meta/StrataLint/scripts/lean-report-pair.sh \
    Meta/StrataLint/StrataLint.Engine/packages.lock.json \
    Meta/StrataLint/StrataLint.Cli/packages.lock.json \
    Meta/StrataLint/StrataLint.Scribe/packages.lock.json \
    global.json; do
    if [[ -f "$REPOSITORY/$relative" \
      || ( "$relative" == "Meta/StrataLint/lean-inspector/inspect.sh" && -n "$PRODUCER_OVERRIDE" ) \
      || ( "$relative" == "Meta/StrataLint/lean-inspector/Inspector.lean" && -n "$INSPECTOR_OVERRIDE" ) ]]; then
      printf '%s\n' "$relative"
    fi
  done
}

producer_closure_complete() {
  local directory
  for directory in \
    Meta/StrataLint/StrataLint.Engine \
    Meta/StrataLint/StrataLint.Cli \
    Meta/StrataLint/StrataLint.Scribe; do
    [[ -d "$REPOSITORY/$directory" ]] || return 1
    find "$REPOSITORY/$directory" -type f -name '*.cs' \
      ! -path '*/bin/*' ! -path '*/obj/*' -print -quit | grep -q . || return 1
  done
}

producer_sha256() {
  local manifest="$1"
  local relative
  : > "$manifest"
  : > "${manifest}.unsorted"
  while IFS= read -r relative; do
    append_producer_manifest_entry "${manifest}.unsorted" "$relative" || return 2
  done < <(producer_paths | sort -u)
  if ! producer_closure_complete; then
    printf '%s\n' "unavailable:$ADDRESS_SIDE" >> "${manifest}.unsorted"
  fi
  sort "${manifest}.unsorted" > "$manifest"
  rm -f -- "${manifest}.unsorted"
  hash_file "$manifest"
}

managed_modules() {
  [[ -f "$REPOSITORY/Trureturing.lean" && -d "$REPOSITORY/D5" ]] \
    || { echo "lean-report-input: managed Lean roots are absent" >&2; return 2; }
  printf 'Trureturing\tTrureturing.lean\n'
  find "$REPOSITORY/D5" -type f -name '*.lean' -print \
    | sed "s#^$REPOSITORY/##" \
    | sort \
    | while IFS= read -r path; do
        module="${path%.lean}"
        printf '%s\t%s\n' "${module//\//.}" "$path"
      done
}

component_hashes() {
  local producer_manifest="$TMP_ROOT/producer.manifest"
  local config_manifest="$TMP_ROOT/config.manifest"
  local lakefile lakefile_count=0
  PRODUCER_SHA256="$(producer_sha256 "$producer_manifest")"
  : > "$config_manifest"
  append_manifest_entry "$config_manifest" "lean-toolchain"
  append_manifest_entry "$config_manifest" "lake-manifest.json"
  for lakefile in lakefile.toml lakefile.lean; do
    if [[ -f "$REPOSITORY/$lakefile" ]]; then
      append_manifest_entry "$config_manifest" "$lakefile"
      lakefile_count=$((lakefile_count + 1))
    fi
  done
  [[ "$lakefile_count" -gt 0 ]] || { echo "lean-report-input: repository has no lakefile" >&2; return 2; }
  CONFIG_SHA256="$(hash_file "$config_manifest")"
}

module_manifest() {
  local modules="$TMP_ROOT/modules.tsv"
  managed_modules > "$modules"
  component_hashes
  if [[ -n "$REPORT" ]]; then
    printf '#report_sha256\t%s\n' "$(hash_file "$REPORT")"
  else
    printf '#report_sha256\t-\n'
  fi
  printf '#producer_sha256\t%s\n' "$PRODUCER_SHA256"
  python3 - "$REPOSITORY" "$modules" "$PRODUCER_SHA256" "$CONFIG_SHA256" <<'PY'
import hashlib
import pathlib
import re
import sys

root, modules_file, producer, config = sys.argv[1:]
root = pathlib.Path(root)
entries = [line.rstrip("\n").split("\t") for line in pathlib.Path(modules_file).read_text().splitlines()]
paths = dict(entries)
imports = {}
unparseable = set()
pattern = re.compile(r"^import[ \t]+([A-Za-z0-9_.]+)[ \t]*$")
import_token = re.compile(r"(?:^|[ \t])import(?:[ \t]|$)")
for module, relative in entries:
    managed = []
    for line in (root / relative).read_text(encoding="utf-8").splitlines():
        if line.lstrip().startswith("--") or import_token.search(line) is None:
            continue
        match = pattern.fullmatch(line)
        if match is None:
            unparseable.add(module)
            continue
        imported = match.group(1)
        if imported == "Trureturing" or imported.startswith("D5."):
            if imported not in paths:
                raise SystemExit(f"lean-report-input: managed import is absent: {imported} (from {relative})")
            managed.append(imported)
    imports[module] = managed

memo = {}
def closure(module, visiting=()):
    if module in visiting:
        raise SystemExit(f"lean-report-input: managed import cycle at {module}")
    if module not in memo:
        result = {module}
        for dependency in imports[module]:
            result.update(closure(dependency, visiting + (module,)))
        memo[module] = result
    return memo[module]

for module, relative in entries:
    preimage = ["schema=stratalint-lean-report-module-input-v1", f"module={module}",
                f"producer_sha256={producer}", f"config_sha256={config}"]
    dependencies = closure(module)
    for dependency in sorted(dependencies):
        digest = hashlib.sha256((root / paths[dependency]).read_bytes()).hexdigest()
        preimage.append(f"{digest}  {dependency}")
    key = hashlib.sha256(("\n".join(preimage) + "\n").encode()).hexdigest()
    prefix = "unparseable:" if dependencies & unparseable else ""
    print(f"{module}\t{relative}\t{prefix}{key}")
PY
}

verify_module_manifest() {
  [[ -n "$MANIFEST" && "$MANIFEST" == /* && -s "$MANIFEST" ]] \
    || { echo "lean-report-input: module manifest is missing" >&2; return 2; }
  local declared_report declared_producer actual_report attested_producer
  declared_report="$(awk -F '\t' '$1 == "#report_sha256" { print $2 }' "$MANIFEST")"
  declared_producer="$(awk -F '\t' '$1 == "#producer_sha256" { print $2 }' "$MANIFEST")"
  actual_report="$(hash_file "$REPORT")"
  attested_producer="$(awk -F '=' '$1 == "producer_sha256" { print $2 }' "${REPORT}.input.attestation" 2>/dev/null || true)"
  [[ "$declared_report" =~ ^[0-9a-f]{64}$ && "$declared_report" == "$actual_report" ]] \
    || { echo "lean-report-input: module manifest report SHA mismatch" >&2; return 2; }
  [[ "$declared_producer" =~ ^[0-9a-f]{64}$ && "$declared_producer" == "$attested_producer" ]] \
    || { echo "lean-report-input: module manifest producer mismatch" >&2; return 2; }
}

repository_address() {
  local resident_manifest="$TMP_ROOT/resident-inspector.manifest"
  local sources_manifest="$TMP_ROOT/sources.manifest"
  local sources_list="$TMP_ROOT/sources.list"
  local config_manifest="$TMP_ROOT/config.manifest"
  local preimage="$TMP_ROOT/repository-input.preimage"
  local resident_sha256 sources_sha256 config_sha256 lakefile_count=0 lakefile

  resident_sha256="$(producer_sha256 "$resident_manifest")"

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
  REPORT_SHA256="$actual"
}

case "$COMMAND" in
  address)
    repository_address
    ;;
  modules)
    managed_modules
    ;;
  manifest)
    module_manifest
    ;;
  verify-manifest)
    verify_module_manifest
    ;;
  verify)
    verify_report_sha
    [[ -f "${REPORT}.input.attestation" ]] \
      || { echo "lean-report-input: production input attestation is missing; run make lean-report first" >&2; exit 2; }
    schema=""
    declared=""
    producer=""
    attested_report=""
    extra=""
    {
      IFS= read -r schema || true
      IFS= read -r declared || true
      IFS= read -r producer || true
      IFS= read -r attested_report || true
      IFS= read -r extra || true
    } < "${REPORT}.input.attestation"
    [[ "$schema" == "schema=stratalint-lean-report-input-attestation-v1" ]] \
      || { echo "lean-report-input: production input attestation is malformed or stale; run make lean-report first" >&2; exit 2; }
    [[ "$declared" =~ ^repository_input_sha256=[0-9a-f]{64}$ \
      && "$producer" =~ ^producer_sha256=[0-9a-f]{64}$ \
      && "$attested_report" == "report_sha256=$REPORT_SHA256" \
      && -z "$extra" ]] \
      || { echo "lean-report-input: production input attestation is malformed or stale; run make lean-report first" >&2; exit 2; }
    declared="${declared#repository_input_sha256=}"
    read -r address _ <<< "$(repository_address)"
    [[ "$declared" == "$address" ]] \
      || { echo "lean-report-input: raw Lean report is stale for current repository inputs; run make lean-report first" >&2; exit 2; }
    ;;
esac
