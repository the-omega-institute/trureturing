#!/usr/bin/env bash
set -euo pipefail

export LC_ALL=C

PRODUCER=""
LAKE_BIN=""
CANDIDATE_ROOT=""
CANDIDATE_OUTPUT=""
BASELINE_ROOT=""
BASELINE_OUTPUT=""
SINGLE=0
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
SUPERVISOR="$SCRIPT_DIR/report/report-supervisor.sh"
INPUT_HELPER="$SCRIPT_DIR/report/lean-report-input.sh"
# Local devloop opt-in only: a host/UID-scoped content-addressed report cache.
# Never set in CI, so CI behaviour is byte-for-byte unchanged.
CACHE_ROOT="${STRATALINT_REPORT_CACHE_ROOT:-}"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --producer) PRODUCER="$2"; shift 2 ;;
    --lake-bin) LAKE_BIN="$2"; shift 2 ;;
    --candidate-root) CANDIDATE_ROOT="$2"; shift 2 ;;
    --candidate-output) CANDIDATE_OUTPUT="$2"; shift 2 ;;
    --baseline-root) BASELINE_ROOT="$2"; shift 2 ;;
    --baseline-output) BASELINE_OUTPUT="$2"; shift 2 ;;
    --single) SINGLE=1; shift ;;
    *) echo "lean-report-pair: unknown argument '$1'" >&2; exit 2 ;;
  esac
done

[[ -n "$PRODUCER" && "$PRODUCER" == /* && -x "$PRODUCER" ]] \
  || { echo "lean-report-pair: --producer requires an absolute executable" >&2; exit 2; }
[[ -n "$LAKE_BIN" && "$LAKE_BIN" == /* && -x "$LAKE_BIN" ]] \
  || { echo "lean-report-pair: --lake-bin requires an absolute executable" >&2; exit 2; }
[[ -d "$CANDIDATE_ROOT" ]] \
  || { echo "lean-report-pair: candidate root is absent" >&2; exit 2; }
[[ -n "$CANDIDATE_OUTPUT" && "$CANDIDATE_OUTPUT" == /* ]] \
  || { echo "lean-report-pair: candidate output must be absolute" >&2; exit 2; }
if [[ "$SINGLE" == "0" ]]; then
  [[ -d "$BASELINE_ROOT" ]] \
    || { echo "lean-report-pair: baseline root is absent" >&2; exit 2; }
  [[ -n "$BASELINE_OUTPUT" && "$BASELINE_OUTPUT" == /* ]] \
    || { echo "lean-report-pair: baseline output must be absolute" >&2; exit 2; }
fi
[[ -x "$SUPERVISOR" ]] \
  || { echo "lean-report-pair: report supervisor is absent" >&2; exit 2; }
[[ -x "$INPUT_HELPER" ]] \
  || { echo "lean-report-pair: report input helper is absent" >&2; exit 2; }

PRODUCER="$(cd "$(dirname "$PRODUCER")" && pwd -P)/$(basename "$PRODUCER")"
CANDIDATE_ROOT="$(cd "$CANDIDATE_ROOT" && pwd -P)"
if [[ "$SINGLE" == "0" ]]; then BASELINE_ROOT="$(cd "$BASELINE_ROOT" && pwd -P)"; fi
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

fingerprint() {
  local root="$1"
  local side="$2"
  local producer_manifest="$TMP_ROOT/$side-producer.manifest"
  local preimage="$TMP_ROOT/$side-input.preimage"

  : > "$producer_manifest"
  printf '%s  inspect.sh\n' "$(hash_file "$PRODUCER")" >> "$producer_manifest"
  printf '%s  Inspector.lean\n' "$(hash_file "$INSPECTOR")" >> "$producer_manifest"
  local producer_sha256
  producer_sha256="$(hash_file "$producer_manifest")"

  local repository_address resident_sha256 sources_sha256 config_sha256
  read -r repository_address resident_sha256 sources_sha256 config_sha256 \
    <<< "$("$INPUT_HELPER" address --repository "$root")"

  {
    printf '%s\n' "schema=stratalint-lean-report-input-v1"
    printf 'producer_sha256=%s\n' "$producer_sha256"
    printf 'repository_inspector_sha256=%s\n' "$resident_sha256"
    printf 'lean_sources_sha256=%s\n' "$sources_sha256"
    printf 'lean_config_sha256=%s\n' "$config_sha256"
  } > "$preimage"
  printf '%s %s %s %s %s %s\n' \
    "$(hash_file "$preimage")" \
    "$producer_sha256" \
    "$resident_sha256" \
    "$sources_sha256" \
    "$config_sha256" \
    "$repository_address"
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

# --- Content-addressed canonical-report cache (local devloop opt-in) -----------
# Ported from CI (.github/workflows/ci.yml, key
# stratalint-canonical-lean-report-v1-<address>). Enabled only when
# STRATALINT_REPORT_CACHE_ROOT is set; CI never sets it. A cache entry is a
# directory named by the report's full content address holding the complete
# verified bundle (report + .sha256 + .input.attestation + .provenance.json).
# Serving is FAIL-CLOSED: every hit is re-verified against the CURRENT tree, and
# any anomaly evicts the entry and falls through to a fresh production. Only a
# producer-rc=0, verify_report()-clean report is ever stored. Mis-serving would
# require BOTH a sha256 content-address collision AND passing the input-helper
# re-verification (a second, independent sha256 over the live tree) — impossible.

cache_evict() {
  local address="$1"
  [[ -n "$CACHE_ROOT" && "$address" =~ ^[0-9a-f]{64}$ ]] || return 0
  rm -rf -- "$CACHE_ROOT/$address" 2>/dev/null || true
}

# Serve $output (report + .sha256 + .input.attestation) from the cache entry for
# content address $address, re-verified against repository $root. Sets
# LAST_REPORT_SHA256 and returns 0 on a verified hit; returns 1 on miss/anomaly
# (any partial output removed, offending entry evicted). Never acquires a slot.
cache_try_restore() {
  local address="$1"
  local root="$2"
  local output="$3"
  [[ -n "$CACHE_ROOT" && "$address" =~ ^[0-9a-f]{64}$ ]] || return 1
  local entry="$CACHE_ROOT/$address"
  local report="$entry/raw-lean-report.json"
  # Completeness: the whole stored bundle must be present before we trust it.
  [[ -s "$report" && -s "${report}.sha256" \
    && -s "${report}.input.attestation" && -s "${report}.provenance.json" ]] \
    || return 1
  local declared="" declared_name=""
  read -r declared declared_name < "${report}.sha256" || true
  [[ "$declared" =~ ^[0-9a-f]{64}$ ]] || { cache_evict "$address"; return 1; }
  rm -f -- "$output" "${output}.sha256" "${output}.provenance.json" \
    "${output}.input.attestation"
  mkdir -p "$(dirname "$output")"
  if ! { cp "$report" "$output" \
    && cp "${report}.input.attestation" "${output}.input.attestation"; }; then
    cache_evict "$address"
    rm -f -- "$output" "${output}.input.attestation"
    return 1
  fi
  local actual
  actual="$(hash_file "$output")"
  if [[ "$actual" != "$declared" ]]; then
    cache_evict "$address"
    rm -f -- "$output" "${output}.input.attestation"
    return 1
  fi
  # Re-stamp the sidecar for this output's basename so it is self-consistent.
  write_sidecar "$output" "$actual"
  # Re-derive the repository address from the CURRENT tree and confirm it matches
  # the stored attestation; rejects any key skew or collision. Fail-closed.
  if ! "$INPUT_HELPER" verify --repository "$root" --report "$output" >/dev/null 2>&1; then
    cache_evict "$address"
    rm -f -- "$output" "${output}.sha256" "${output}.input.attestation"
    return 1
  fi
  LAST_REPORT_SHA256="$actual"
  return 0
}

# Atomically publish the fully-materialised bundle at $output under $address.
# No-op unless caching is enabled and the complete bundle exists. Entries are
# content-addressed and immutable, so a concurrent winner is tolerated.
cache_store() {
  local address="$1"
  local output="$2"
  [[ -n "$CACHE_ROOT" && "$address" =~ ^[0-9a-f]{64}$ ]] || return 0
  [[ -s "$output" && -s "${output}.sha256" \
    && -s "${output}.input.attestation" && -s "${output}.provenance.json" ]] \
    || return 0
  local entry="$CACHE_ROOT/$address"
  [[ -e "$entry" ]] && return 0
  mkdir -p "$CACHE_ROOT" 2>/dev/null || return 0
  local tmp
  tmp="$(mktemp -d "$CACHE_ROOT/.tmp.$$.XXXXXXXX" 2>/dev/null)" || return 0
  local report="$tmp/raw-lean-report.json"
  # Best-effort: any copy or sidecar-write failure discards the temp and leaves the
  # gate untouched (never fails admission on a cache-write error).
  if ! { cp "$output" "$report" \
    && cp "${output}.input.attestation" "${report}.input.attestation" \
    && cp "${output}.provenance.json" "${report}.provenance.json" \
    && printf '%s  raw-lean-report.json\n' "$(hash_file "$report")" > "${report}.sha256"; }; then
    rm -rf -- "$tmp"
    return 0
  fi
  if [[ -e "$entry" ]] || ! mv "$tmp" "$entry" 2>/dev/null; then
    rm -rf -- "$tmp"
  fi
  return 0
}

produce_report() {
  local side="$1"
  local root="$2"
  local output="$3"
  local address="$4"
  rm -f -- "$output" "${output}.sha256" "${output}.provenance.json" \
    "${output}.input.attestation"
  mkdir -p "$(dirname "$output")"
  # Cache lookup precedes any slot acquisition or producer run.
  if cache_try_restore "$address" "$root" "$output"; then
    LAST_REPORT_MODE="cached"
    return 0
  fi
  "$SUPERVISOR" --role "lean-producer-$side" --lean-slot -- \
    env LAKE_BIN="$LAKE_BIN" "$PRODUCER" --repository "$root" --output "$output"
  verify_report "$output"
  LAST_REPORT_MODE="produced"
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

write_input_attestation() {
  local output="$1"
  local repository_sha256="$2"
  local producer_sha256="$3"
  local report_sha256="$4"
  {
    printf '%s\n' "schema=stratalint-lean-report-input-attestation-v1"
    printf 'repository_input_sha256=%s\n' "$repository_sha256"
    printf 'producer_sha256=%s\n' "$producer_sha256"
    printf 'report_sha256=%s\n' "$report_sha256"
  } > "${output}.input.attestation"
}

read -r candidate_address candidate_producer candidate_resident candidate_sources candidate_config candidate_repository \
  <<< "$(fingerprint "$CANDIDATE_ROOT" candidate)"
printf 'LEAN_REPORT_INPUT side=candidate content_address=sha256:%s producer_sha256=%s repository_inspector_sha256=%s lean_sources_sha256=%s lean_config_sha256=%s\n' \
  "$candidate_address" "$candidate_producer" "$candidate_resident" "$candidate_sources" "$candidate_config"

produce_report candidate "$CANDIDATE_ROOT" "$CANDIDATE_OUTPUT" "$candidate_address"
candidate_report_sha256="$LAST_REPORT_SHA256"
candidate_mode="$LAST_REPORT_MODE"
write_provenance \
  candidate "$CANDIDATE_OUTPUT" "$candidate_mode" candidate \
  "$candidate_address" "$candidate_producer" "$candidate_resident" \
  "$candidate_sources" "$candidate_config" "$candidate_report_sha256"
write_input_attestation \
  "$CANDIDATE_OUTPUT" "$candidate_repository" "$candidate_producer" "$candidate_report_sha256"
if [[ "$candidate_mode" == "produced" ]]; then
  cache_store "$candidate_address" "$CANDIDATE_OUTPUT"
fi

if [[ "$SINGLE" == "1" ]]; then exit 0; fi

read -r baseline_address baseline_producer baseline_resident baseline_sources baseline_config baseline_repository \
  <<< "$(fingerprint "$BASELINE_ROOT" baseline)"
printf 'LEAN_REPORT_INPUT side=baseline content_address=sha256:%s producer_sha256=%s repository_inspector_sha256=%s lean_sources_sha256=%s lean_config_sha256=%s\n' \
  "$baseline_address" "$baseline_producer" "$baseline_resident" "$baseline_sources" "$baseline_config"

if [[ "$candidate_address" == "$baseline_address" ]]; then
  rm -f -- "$BASELINE_OUTPUT" "${BASELINE_OUTPUT}.sha256" \
    "${BASELINE_OUTPUT}.provenance.json" "${BASELINE_OUTPUT}.input.attestation"
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
  write_input_attestation \
    "$BASELINE_OUTPUT" "$baseline_repository" "$baseline_producer" "$verify_report_copy_sha256"
else
  produce_report baseline "$BASELINE_ROOT" "$BASELINE_OUTPUT" "$baseline_address"
  baseline_report_sha256="$LAST_REPORT_SHA256"
  baseline_mode="$LAST_REPORT_MODE"
  write_provenance \
    baseline "$BASELINE_OUTPUT" "$baseline_mode" baseline \
    "$baseline_address" "$baseline_producer" "$baseline_resident" \
    "$baseline_sources" "$baseline_config" "$baseline_report_sha256"
  write_input_attestation \
    "$BASELINE_OUTPUT" "$baseline_repository" "$baseline_producer" "$baseline_report_sha256"
  if [[ "$baseline_mode" == "produced" ]]; then
    cache_store "$baseline_address" "$BASELINE_OUTPUT"
  fi
fi
