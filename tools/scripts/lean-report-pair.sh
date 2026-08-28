#!/usr/bin/env bash
set -euo pipefail

export LC_ALL=C

PRODUCER=""
LAKE_BIN=""
CANDIDATE_ROOT=""
CANDIDATE_OUTPUT=""
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
SUPERVISOR="$SCRIPT_DIR/report/report-supervisor.sh"
INPUT_HELPER="$SCRIPT_DIR/report/lean-report-input.sh"
# Opt-in host/UID-scoped content-addressed report cache. Local entry points use
# the persistent host cache; CI may supply a runner-temporary root containing an
# attested stale dev report for the producer's existing delta path.
CACHE_ROOT="${STRATALINT_REPORT_CACHE_ROOT:-}"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --producer) PRODUCER="$2"; shift 2 ;;
    --lake-bin) LAKE_BIN="$2"; shift 2 ;;
    --candidate-root) CANDIDATE_ROOT="$2"; shift 2 ;;
    --candidate-output) CANDIDATE_OUTPUT="$2"; shift 2 ;;
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
[[ -x "$SUPERVISOR" ]] \
  || { echo "lean-report-pair: report supervisor is absent" >&2; exit 2; }
[[ -x "$INPUT_HELPER" ]] \
  || { echo "lean-report-pair: report input helper is absent" >&2; exit 2; }

PRODUCER="$(cd "$(dirname "$PRODUCER")" && pwd -P)/$(basename "$PRODUCER")"
CANDIDATE_ROOT="$(cd "$CANDIDATE_ROOT" && pwd -P)"
INSPECTOR="$(dirname "$PRODUCER")/Inspector.lean"
[[ -f "$INSPECTOR" ]] \
  || { echo "lean-report-pair: producer Inspector.lean is absent" >&2; exit 2; }

TMP_ROOT="$(mktemp -d)"
STAGING_DIRS=()

cleanup() {
  local directory
  if [[ ${#STAGING_DIRS[@]} -gt 0 ]]; then
    for directory in "${STAGING_DIRS[@]}"; do rm -rf -- "$directory"; done
  fi
  rm -rf -- "$TMP_ROOT"
}
finish_pair() {
  local rc=$?
  trap - EXIT HUP INT TERM
  set +e
  cleanup
  exit "$rc"
}
trap finish_pair EXIT
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
  local preimage="$TMP_ROOT/input.preimage"

  local repository_address resident_sha256 sources_sha256 config_sha256 address_output
  address_output="$("$INPUT_HELPER" address --repository "$root" --producer "$PRODUCER" --inspector "$INSPECTOR")" || return 2
  read -r repository_address resident_sha256 sources_sha256 config_sha256 <<< "$address_output"
  local producer_sha256="$resident_sha256"

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
  [[ -s "${output}.materials.zip" ]] \
    || { echo "lean-report-pair: producer left no material archive: $output" >&2; return 2; }
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

# --- Content-addressed canonical-report cache (local opt-in) -----------
# Ported from CI (.github/workflows/ci.yml, key
# stratalint-canonical-lean-report-v2-<address>). Enabled only when
# STRATALINT_REPORT_CACHE_ROOT is set. A cache entry is a
# directory named by the report's full content address holding the complete
# bundle (report + three validation sidecars + material archive).
#
# SECURITY MODEL (honest): the re-verification below anchors only PUBLIC
# repository-tree inputs (Trureturing.lean, D5, toolchain, manifest) — it is NOT a
# secret trust anchor. Anyone who can write into the cache directory can forge an
# entry whose .sha256 and .input.attestation self-consistently pass re-verification
# (all derived from public files). Cache correctness therefore DEPENDS on the cache
# directory being writable only by this UID: entries are trusted only when
# $CACHE_ROOT is owned by us and is not group/other-writable (cache_root_trusted),
# and cache_store creates it 0700. A foreign-owned or world-writable root (e.g.
# pre-created in a shared /tmp) is never trusted and falls through to a fresh
# production. On top of that ownership guarantee, the re-verification stays a
# fail-closed defence against key skew and stale inputs, and only producer-rc=0,
# verify_report()-clean reports are ever stored.

# Trust the cache only when its root exists, is owned by the current user, and
# grants no group/other write bit — so no other non-root user could have planted
# or altered an entry. Cross-platform stat: BSD (%u/%Lp) then GNU (%u/%a).
cache_root_trusted() {
  [[ -n "$CACHE_ROOT" && -d "$CACHE_ROOT" ]] || return 1
  local owner perm
  if owner="$(stat -f '%u' "$CACHE_ROOT" 2>/dev/null)" \
    && perm="$(stat -f '%Lp' "$CACHE_ROOT" 2>/dev/null)"; then
    :
  elif owner="$(stat -c '%u' "$CACHE_ROOT" 2>/dev/null)" \
    && perm="$(stat -c '%a' "$CACHE_ROOT" 2>/dev/null)"; then
    :
  else
    return 1
  fi
  [[ "$owner" == "$(id -u)" ]] || return 1
  [[ "$perm" =~ ^[0-7]+$ ]] || return 1
  (( (8#$perm & 8#22) == 0 )) || return 1
  return 0
}

cache_evict() {
  local address="$1"
  [[ -n "$CACHE_ROOT" && "$address" =~ ^[0-9a-f]{64}$ ]] || return 0
  rm -rf -- "$CACHE_ROOT/$address" 2>/dev/null || true
}

cache_provenance_matches() {
  local provenance="$1"
  local address="$2"
  local report_sha256="$3"
  python3 - "$provenance" "$address" "$report_sha256" \
    "${candidate_producer:-}" "${candidate_resident:-}" \
    "${candidate_sources:-}" "${candidate_config:-}" <<'PY'
import json
import pathlib
import sys

path, address, report_sha, producer, resident, sources, config = sys.argv[1:]
try:
    value = json.loads(pathlib.Path(path).read_text(encoding="utf-8"))
except (OSError, UnicodeError, ValueError, json.JSONDecodeError):
    raise SystemExit(1)
expected_keys = {
    "schema", "side", "mode", "source_side", "input_address",
    "producer_sha256", "repository_inspector_sha256", "lean_sources_sha256",
    "lean_config_sha256", "report_sha256",
}
if (set(value) != expected_keys
        or value.get("schema") != "stratalint-lean-report-provenance-v1"
        or value.get("side") != "candidate"
        or value.get("source_side") != "candidate"
        or value.get("mode") not in ("produced", "cached")
        or value.get("input_address") != "sha256:" + address
        or value.get("producer_sha256") != producer
        or value.get("repository_inspector_sha256") != resident
        or value.get("lean_sources_sha256") != sources
        or value.get("lean_config_sha256") != config
        or value.get("report_sha256") != report_sha):
    raise SystemExit(1)
PY
}

# Serve the complete bundle at $output from the cache entry for
# content address $address, re-verified against repository $root. Sets
# LAST_REPORT_SHA256 and returns 0 on a verified hit; returns 1 on miss/anomaly
# (any partial output removed, offending entry evicted), or 2 on destination I/O
# failure. Never acquires a slot or touches a live bundle.
cache_try_restore() {
  local address="$1"
  local root="$2"
  local output="$3"
  [[ -n "$CACHE_ROOT" && "$address" =~ ^[0-9a-f]{64}$ ]] || return 1
  # Refuse to trust a cache root that any other non-root user could have written.
  cache_root_trusted || return 1
  local entry="$CACHE_ROOT/$address"
  local report="$entry/raw-lean-report.json"
  # Completeness: the whole stored bundle must be present before we trust it.
  [[ -s "$report" && -s "${report}.sha256" \
    && -s "${report}.input.attestation" && -s "${report}.provenance.json" \
    && -s "${report}.materials.zip" ]] \
    || { cache_evict "$address"; return 1; }
  local declared="" declared_name=""
  read -r declared declared_name < "${report}.sha256" || true
  [[ "$declared" =~ ^[0-9a-f]{64}$ \
    && "$declared_name" == "raw-lean-report.json" \
    && "$(awk 'END {print NR}' "${report}.sha256")" == "1" ]] \
    || { cache_evict "$address"; return 1; }
  rm -rf -- "$output" "${output}.sha256" "${output}.provenance.json" \
    "${output}.input.attestation" "${output}.materials.zip"
  mkdir -p "$(dirname "$output")"
  if ! { cp "$report" "$output" \
    && cp "${report}.input.attestation" "${output}.input.attestation" \
    && cp "${report}.provenance.json" "${output}.provenance.json" \
    && cp "${report}.materials.zip" "${output}.materials.zip"; }; then
    rm -rf -- "$output" "${output}.sha256" "${output}.provenance.json" \
      "${output}.input.attestation" "${output}.materials.zip"
    return 2
  fi
  local actual
  actual="$(hash_file "$output")"
  if [[ "$actual" != "$declared" ]]; then
    cache_evict "$address"
    rm -rf -- "$output" "${output}.provenance.json" \
      "${output}.input.attestation" "${output}.materials.zip"
    return 1
  fi
  # Validate the stored provenance before treating an exact-address hit as
  # authoritative.  prepare_bundle rewrites the staged provenance later, so
  # this check must happen here or a damaged cache sidecar could be masked.
  if ! cache_provenance_matches "${output}.provenance.json" "$address" "$actual"; then
    cache_evict "$address"
    rm -rf -- "$output" "${output}.sha256" \
      "${output}.input.attestation" "${output}.provenance.json" \
      "${output}.materials.zip"
    return 1
  fi
  # Re-stamp the sidecar for this output's basename so it is self-consistent.
  write_sidecar "$output" "$actual"
  # Re-derive the repository address from the CURRENT tree and confirm it matches
  # the stored attestation; rejects any key skew or collision. Fail-closed.
  if ! "$INPUT_HELPER" verify --repository "$root" --report "$output" \
    --producer "$PRODUCER" --inspector "$INSPECTOR" >/dev/null 2>&1; then
    cache_evict "$address"
    rm -rf -- "$output" "${output}.sha256" "${output}.provenance.json" \
      "${output}.input.attestation" "${output}.materials.zip"
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
    && -s "${output}.input.attestation" && -s "${output}.provenance.json" \
    && -s "${output}.materials.zip" ]] \
    || return 0
  local entry="$CACHE_ROOT/$address"
  [[ -e "$entry" ]] && return 0
  mkdir -p "$CACHE_ROOT" 2>/dev/null || return 0
  # Lock the root to this UID (harmless if we already own a 0700 dir; a no-op fail
  # if some other user pre-created it, in which case the trust check below refuses
  # to store). Never write into a root we cannot secure.
  chmod 700 "$CACHE_ROOT" 2>/dev/null || true
  cache_root_trusted || return 0
  local tmp
  tmp="$(mktemp -d "$CACHE_ROOT/.tmp.$$.XXXXXXXX" 2>/dev/null)" || return 0
  local report="$tmp/raw-lean-report.json"
  # Best-effort: any copy or sidecar-write failure discards the temp and leaves the
  # gate untouched (never fails admission on a cache-write error).
  if ! { cp "$output" "$report" \
    && cp "${output}.input.attestation" "${report}.input.attestation" \
    && cp "${output}.provenance.json" "${report}.provenance.json" \
    && cp "${output}.materials.zip" "${report}.materials.zip" \
    && printf '%s  raw-lean-report.json\n' "$(hash_file "$report")" > "${report}.sha256"; }; then
    rm -rf -- "$tmp"
    return 0
  fi
  if [[ -e "$entry" ]] || ! mv "$tmp" "$entry" 2>/dev/null; then
    rm -rf -- "$tmp"
  fi
  return 0
}

materialize_report() {
  local root="$1"
  local output="$2"
  local address="$3"
  # Cache lookup precedes any slot acquisition or producer run.
  if cache_try_restore "$address" "$root" "$output"; then
    LAST_REPORT_MODE="cached"
    return 0
  else
    local cache_rc=$?
    [[ "$cache_rc" == "1" ]] || return "$cache_rc"
  fi
  # Per-module reuse is disabled. Before enabling it, producer identity must cover
  # the actually selected MSBuild SDK and dotnet runtime plus the bytes of every
  # actually loaded NuGet package, analyzer, and source generator (or hash the DLL
  # that is actually executed). global.json latestMinor can make 10.0.103 select
  # SDK 10.0.201, so one producer SHA can otherwise execute code built by different
  # toolchains. Keep production on the complete-report path until that is solved.
  "$SUPERVISOR" --role lean-producer --lean-slot -- \
    env LAKE_BIN="$LAKE_BIN" \
      STRATALINT_REPORT_INPUT_ADDRESS="$input_address" \
      STRATALINT_REPORT_REPOSITORY_SHA256="$repository_sha256" \
      STRATALINT_REPORT_PRODUCER_SHA256="$producer_sha256" \
      STRATALINT_REPORT_RESIDENT_SHA256="$resident_sha256" \
      STRATALINT_REPORT_SOURCES_SHA256="$sources_sha256" \
      STRATALINT_REPORT_CONFIG_SHA256="$config_sha256" \
      "$PRODUCER" --repository "$root" --output "$output"
  verify_report "$output"
  LAST_REPORT_MODE="produced"
}

write_sidecar() {
  local output="$1"
  local sha256="$2"
  printf '%s  %s\n' "$sha256" "$(basename "$output")" > "${output}.sha256"
}

write_provenance() {
  local output="$1"
  local mode="$2"
  local input_address="$3"
  local producer_sha256="$4"
  local resident_sha256="$5"
  local sources_sha256="$6"
  local config_sha256="$7"
  local report_sha256="$8"
  printf '{"schema":"stratalint-lean-report-provenance-v1","side":"%s","mode":"%s","source_side":"%s","input_address":"sha256:%s","producer_sha256":"%s","repository_inspector_sha256":"%s","lean_sources_sha256":"%s","lean_config_sha256":"%s","report_sha256":"%s"}\n' \
    candidate "$mode" candidate "$input_address" "$producer_sha256" \
    "$resident_sha256" "$sources_sha256" "$config_sha256" "$report_sha256" \
    > "${output}.provenance.json"
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

verify_bundle() {
  local root="$1"
  local output="$2"
  local mode="$3"
  local input_address="$4"
  local producer_sha256="$5"
  local resident_sha256="$6"
  local sources_sha256="$7"
  local config_sha256="$8"
  local repository_sha256="$9"
  local report_sha256="${10}"
  local expected_provenance="$TMP_ROOT/expected.provenance.json"
  local expected_attestation="$TMP_ROOT/expected.input.attestation"

  [[ -s "${output}.materials.zip" ]] \
    || { echo "lean-report-pair: producer left no material archive: $output" >&2; return 2; }
  "$INPUT_HELPER" verify --repository "$root" --report "$output" \
    --producer "$PRODUCER" --inspector "$INSPECTOR" >/dev/null

  printf '{"schema":"stratalint-lean-report-provenance-v1","side":"candidate","mode":"%s","source_side":"candidate","input_address":"sha256:%s","producer_sha256":"%s","repository_inspector_sha256":"%s","lean_sources_sha256":"%s","lean_config_sha256":"%s","report_sha256":"%s"}\n' \
    "$mode" "$input_address" "$producer_sha256" \
    "$resident_sha256" "$sources_sha256" "$config_sha256" "$report_sha256" \
    > "$expected_provenance"
  cmp -s "$expected_provenance" "${output}.provenance.json" \
    || { echo "lean-report-pair: provenance sidecar mismatch: $output" >&2; return 2; }
  {
    printf '%s\n' "schema=stratalint-lean-report-input-attestation-v1"
    printf 'repository_input_sha256=%s\n' "$repository_sha256"
    printf 'producer_sha256=%s\n' "$producer_sha256"
    printf 'report_sha256=%s\n' "$report_sha256"
  } > "$expected_attestation"
  cmp -s "$expected_attestation" "${output}.input.attestation" \
    || { echo "lean-report-pair: input attestation mismatch: $output" >&2; return 2; }
}

create_staging_output() {
  local live_output="$1"
  local parent
  local directory
  parent="$(dirname "$live_output")"
  mkdir -p "$parent"
  directory="$(mktemp -d "$parent/.lean-report-bundle.XXXXXXXX")"
  STAGING_DIRS+=("$directory")
  LAST_STAGING_OUTPUT="$directory/$(basename "$live_output")"
}

prepare_bundle() {
  local root="$1"
  local live_output="$2"
  local input_address="$3"
  local producer_sha256="$4"
  local resident_sha256="$5"
  local sources_sha256="$6"
  local config_sha256="$7"
  local repository_sha256="$8"

  local cache_ensure="${root}/tools/scripts/worktree/lean-cache-ensure.sh"
  [[ -f "$cache_ensure" && -r "$cache_ensure" ]] \
    || { echo "lean-report-pair: cache ensure is absent or not a readable regular file: $cache_ensure" >&2; return 2; }
  "$BASH" "$cache_ensure"

  create_staging_output "$live_output"
  local staged_output="$LAST_STAGING_OUTPUT"
  materialize_report "$root" "$staged_output" "$input_address"
  local mode="$LAST_REPORT_MODE"
  local report_sha256="$LAST_REPORT_SHA256"
  write_provenance \
    "$staged_output" "$mode" "$input_address" \
    "$producer_sha256" "$resident_sha256" "$sources_sha256" \
    "$config_sha256" "$report_sha256"
  write_input_attestation \
    "$staged_output" "$repository_sha256" "$producer_sha256" "$report_sha256"
  verify_bundle \
    "$root" "$staged_output" "$mode" "$input_address" \
    "$producer_sha256" "$resident_sha256" "$sources_sha256" \
    "$config_sha256" "$repository_sha256" "$report_sha256"
  LAST_BUNDLE_OUTPUT="$staged_output"
  LAST_BUNDLE_MODE="$mode"
  LAST_BUNDLE_SHA256="$report_sha256"
}

publish_bundle() {
  local staged="$1"
  local live="$2"
  local suffix
  rm -rf -- "${live}.materials" "${live}.logs"
  for suffix in "" ".sha256" ".input.attestation" ".provenance.json" ".materials.zip"; do
    mv -f "${staged}${suffix}" "${live}${suffix}"
  done
  if [[ -d "${staged}.logs" ]]; then
    mv "${staged}.logs" "${live}.logs"
  fi
}

emit_provenance_receipt() {
  local output="$1"
  local mode="$2"
  local input_address="$3"
  local report_sha256="$4"
  printf 'LEAN_REPORT_PROVENANCE side=candidate mode=%s source_side=candidate input_address=sha256:%s report_sha256=%s attestation=%s\n' \
    "$mode" "$input_address" "$report_sha256" \
    "${output}.provenance.json"
}

read -r candidate_address candidate_producer candidate_resident candidate_sources candidate_config candidate_repository \
  <<< "$(fingerprint "$CANDIDATE_ROOT")"
printf 'LEAN_REPORT_INPUT side=candidate content_address=sha256:%s producer_sha256=%s repository_inspector_sha256=%s lean_sources_sha256=%s lean_config_sha256=%s\n' \
  "$candidate_address" "$candidate_producer" "$candidate_resident" "$candidate_sources" "$candidate_config"

prepare_bundle \
  "$CANDIDATE_ROOT" "$CANDIDATE_OUTPUT" "$candidate_address" \
  "$candidate_producer" "$candidate_resident" "$candidate_sources" \
  "$candidate_config" "$candidate_repository"
candidate_staged_output="$LAST_BUNDLE_OUTPUT"
candidate_report_sha256="$LAST_BUNDLE_SHA256"
candidate_mode="$LAST_BUNDLE_MODE"

publish_bundle "$candidate_staged_output" "$CANDIDATE_OUTPUT"
emit_provenance_receipt \
  "$CANDIDATE_OUTPUT" "$candidate_mode" "$candidate_address" "$candidate_report_sha256"
if [[ "$candidate_mode" == "produced" ]]; then
  cache_store "$candidate_address" "$CANDIDATE_OUTPUT"
fi
