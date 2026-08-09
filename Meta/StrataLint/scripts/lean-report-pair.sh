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
STAGING_DIRS=()
cleanup() {
  local directory
  for directory in "${STAGING_DIRS[@]}"; do rm -rf -- "$directory"; done
  rm -rf -- "$TMP_ROOT"
}
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
# bundle (report + three validation sidecars + producer logs).
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
    && -d "${report}.logs" ]] \
    || { cache_evict "$address"; return 1; }
  local declared="" declared_name=""
  read -r declared declared_name < "${report}.sha256" || true
  [[ "$declared" =~ ^[0-9a-f]{64}$ \
    && "$declared_name" == "raw-lean-report.json" \
    && "$(awk 'END {print NR}' "${report}.sha256")" == "1" ]] \
    || { cache_evict "$address"; return 1; }
  rm -rf -- "$output" "${output}.sha256" "${output}.provenance.json" \
    "${output}.input.attestation" "${output}.logs"
  mkdir -p "$(dirname "$output")"
  if ! { cp "$report" "$output" \
    && cp "${report}.input.attestation" "${output}.input.attestation" \
    && cp "${report}.provenance.json" "${output}.provenance.json" \
    && cp -R "${report}.logs" "${output}.logs"; }; then
    rm -rf -- "$output" "${output}.sha256" "${output}.provenance.json" \
      "${output}.input.attestation" "${output}.logs"
    return 2
  fi
  local actual
  actual="$(hash_file "$output")"
  if [[ "$actual" != "$declared" ]]; then
    cache_evict "$address"
    rm -rf -- "$output" "${output}.provenance.json" \
      "${output}.input.attestation" "${output}.logs"
    return 1
  fi
  # Re-stamp the sidecar for this output's basename so it is self-consistent.
  write_sidecar "$output" "$actual"
  # Re-derive the repository address from the CURRENT tree and confirm it matches
  # the stored attestation; rejects any key skew or collision. Fail-closed.
  if ! "$INPUT_HELPER" verify --repository "$root" --report "$output" >/dev/null 2>&1; then
    cache_evict "$address"
    rm -rf -- "$output" "${output}.sha256" "${output}.provenance.json" \
      "${output}.input.attestation" "${output}.logs"
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
    && -d "${output}.logs" ]] \
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
    && cp -R "${output}.logs" "${report}.logs" \
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
  local side="$1"
  local root="$2"
  local output="$3"
  local address="$4"
  # Cache lookup precedes any slot acquisition or producer run.
  if cache_try_restore "$address" "$root" "$output"; then
    LAST_REPORT_MODE="cached"
    return 0
  else
    local cache_rc=$?
    [[ "$cache_rc" == "1" ]] || return "$cache_rc"
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
  local side="$1"
  local root="$2"
  local output="$3"
  local mode="$4"
  local source_side="$5"
  local input_address="$6"
  local producer_sha256="$7"
  local resident_sha256="$8"
  local sources_sha256="$9"
  local config_sha256="${10}"
  local repository_sha256="${11}"
  local report_sha256="${12}"
  local expected_provenance="$TMP_ROOT/$side-expected.provenance.json"
  local expected_attestation="$TMP_ROOT/$side-expected.input.attestation"

  verify_report "$output"
  [[ "$LAST_REPORT_SHA256" == "$report_sha256" ]] \
    || { echo "lean-report-pair: verified report address changed: $output" >&2; return 2; }
  [[ -d "${output}.logs" && -n "$(find "${output}.logs" -type f -print -quit)" ]] \
    || { echo "lean-report-pair: producer left no log sidecar: $output" >&2; return 2; }
  "$INPUT_HELPER" verify --repository "$root" --report "$output" >/dev/null

  printf '{"schema":"stratalint-lean-report-provenance-v1","side":"%s","mode":"%s","source_side":"%s","input_address":"sha256:%s","producer_sha256":"%s","repository_inspector_sha256":"%s","lean_sources_sha256":"%s","lean_config_sha256":"%s","report_sha256":"%s"}\n' \
    "$side" "$mode" "$source_side" "$input_address" "$producer_sha256" \
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
  local side="$1"
  local root="$2"
  local live_output="$3"
  local input_address="$4"
  local producer_sha256="$5"
  local resident_sha256="$6"
  local sources_sha256="$7"
  local config_sha256="$8"
  local repository_sha256="$9"

  create_staging_output "$live_output"
  local staged_output="$LAST_STAGING_OUTPUT"
  materialize_report "$side" "$root" "$staged_output" "$input_address"
  local mode="$LAST_REPORT_MODE"
  local report_sha256="$LAST_REPORT_SHA256"
  write_provenance \
    "$side" "$staged_output" "$mode" "$side" "$input_address" \
    "$producer_sha256" "$resident_sha256" "$sources_sha256" \
    "$config_sha256" "$report_sha256"
  write_input_attestation \
    "$staged_output" "$repository_sha256" "$producer_sha256" "$report_sha256"
  verify_bundle \
    "$side" "$root" "$staged_output" "$mode" "$side" "$input_address" \
    "$producer_sha256" "$resident_sha256" "$sources_sha256" \
    "$config_sha256" "$repository_sha256" "$report_sha256"
  LAST_BUNDLE_OUTPUT="$staged_output"
  LAST_BUNDLE_MODE="$mode"
  LAST_BUNDLE_SHA256="$report_sha256"
}

prepare_reused_bundle() {
  local root="$1"
  local live_output="$2"
  local source_output="$3"
  local input_address="$4"
  local producer_sha256="$5"
  local resident_sha256="$6"
  local sources_sha256="$7"
  local config_sha256="$8"
  local repository_sha256="$9"
  local report_sha256="${10}"

  create_staging_output "$live_output"
  local staged_output="$LAST_STAGING_OUTPUT"
  cp "$source_output" "$staged_output"
  cp -R "${source_output}.logs" "${staged_output}.logs"
  [[ "$(hash_file "$staged_output")" == "$report_sha256" ]] \
    || { echo "lean-report-pair: reused report copy changed bytes" >&2; return 2; }
  write_sidecar "$staged_output" "$report_sha256"
  write_provenance \
    baseline "$staged_output" reused candidate "$input_address" \
    "$producer_sha256" "$resident_sha256" "$sources_sha256" \
    "$config_sha256" "$report_sha256"
  write_input_attestation \
    "$staged_output" "$repository_sha256" "$producer_sha256" "$report_sha256"
  verify_bundle \
    baseline "$root" "$staged_output" reused candidate "$input_address" \
    "$producer_sha256" "$resident_sha256" "$sources_sha256" \
    "$config_sha256" "$repository_sha256" "$report_sha256"
  LAST_BUNDLE_OUTPUT="$staged_output"
  LAST_BUNDLE_MODE="reused"
  LAST_BUNDLE_SHA256="$report_sha256"
}

publish_bundles() {
  [[ "$#" -ge 2 && $(( $# % 2 )) == 0 ]] \
    || { echo "lean-report-pair: internal publish argument mismatch" >&2; return 2; }
  local -a staged_outputs=()
  local -a live_outputs=()
  local -a backups=()
  local -a existed=()
  local -a suffixes=("" ".sha256" ".input.attestation" ".provenance.json" ".logs")
  local staged live backup suffix source target
  local bundle_index member_index flat_index

  while [[ "$#" -gt 0 ]]; do
    staged_outputs+=("$1")
    live_outputs+=("$2")
    shift 2
  done

  for ((bundle_index = 0; bundle_index < ${#live_outputs[@]}; bundle_index++)); do
    live="${live_outputs[$bundle_index]}"
    if ! backup="$(mktemp -d "$(dirname "$live")/.lean-report-backup.XXXXXXXX")"; then
      rm -rf -- "${backups[@]}"
      return 2
    fi
    backups+=("$backup")
    for ((member_index = 0; member_index < ${#suffixes[@]}; member_index++)); do
      flat_index=$((bundle_index * ${#suffixes[@]} + member_index))
      source="${live}${suffixes[$member_index]}"
      target="$backup/member-$member_index"
      if [[ -e "$source" ]]; then
        existed[$flat_index]=1
        if [[ -d "$source" ]]; then
          cp -R "$source" "$target" || { rm -rf -- "${backups[@]}"; return 2; }
        else
          cp "$source" "$target" || { rm -rf -- "${backups[@]}"; return 2; }
        fi
      else
        existed[$flat_index]=0
      fi
    done
  done

  local publish_failed=0
  trap '' HUP INT TERM
  for ((bundle_index = 0; bundle_index < ${#live_outputs[@]}; bundle_index++)); do
    staged="${staged_outputs[$bundle_index]}"
    live="${live_outputs[$bundle_index]}"
    for suffix in "${suffixes[@]}"; do
      if [[ "$suffix" == ".logs" ]] && ! rm -rf -- "${live}${suffix}"; then
        publish_failed=1
        break 2
      fi
      if ! mv -f "${staged}${suffix}" "${live}${suffix}"; then
        publish_failed=1
        break 2
      fi
    done
  done

  if [[ "$publish_failed" == "1" ]]; then
    local rollback_failed=0
    for ((bundle_index = 0; bundle_index < ${#live_outputs[@]}; bundle_index++)); do
      live="${live_outputs[$bundle_index]}"
      backup="${backups[$bundle_index]}"
      for ((member_index = 0; member_index < ${#suffixes[@]}; member_index++)); do
        flat_index=$((bundle_index * ${#suffixes[@]} + member_index))
        target="${live}${suffixes[$member_index]}"
        if ! rm -rf -- "$target"; then
          rollback_failed=1
          continue
        fi
        if [[ "${existed[$flat_index]}" == "1" ]]; then
          mv "$backup/member-$member_index" "$target" || rollback_failed=1
        fi
      done
    done
    rm -rf -- "${backups[@]}" || true
    trap 'exit 129' HUP
    trap 'exit 130' INT
    trap 'exit 143' TERM
    [[ "$rollback_failed" == "0" ]] \
      || { echo "lean-report-pair: bundle publish rollback failed" >&2; return 2; }
    echo "lean-report-pair: bundle publish failed; prior bundle restored" >&2
    return 2
  fi

  rm -rf -- "${backups[@]}" || true
  trap 'exit 129' HUP
  trap 'exit 130' INT
  trap 'exit 143' TERM
}

emit_provenance_receipt() {
  local side="$1"
  local output="$2"
  local mode="$3"
  local source_side="$4"
  local input_address="$5"
  local report_sha256="$6"
  printf 'LEAN_REPORT_PROVENANCE side=%s mode=%s source_side=%s input_address=sha256:%s report_sha256=%s attestation=%s\n' \
    "$side" "$mode" "$source_side" "$input_address" "$report_sha256" \
    "${output}.provenance.json"
}

read -r candidate_address candidate_producer candidate_resident candidate_sources candidate_config candidate_repository \
  <<< "$(fingerprint "$CANDIDATE_ROOT" candidate)"
printf 'LEAN_REPORT_INPUT side=candidate content_address=sha256:%s producer_sha256=%s repository_inspector_sha256=%s lean_sources_sha256=%s lean_config_sha256=%s\n' \
  "$candidate_address" "$candidate_producer" "$candidate_resident" "$candidate_sources" "$candidate_config"

prepare_bundle \
  candidate "$CANDIDATE_ROOT" "$CANDIDATE_OUTPUT" "$candidate_address" \
  "$candidate_producer" "$candidate_resident" "$candidate_sources" \
  "$candidate_config" "$candidate_repository"
candidate_staged_output="$LAST_BUNDLE_OUTPUT"
candidate_report_sha256="$LAST_BUNDLE_SHA256"
candidate_mode="$LAST_BUNDLE_MODE"

if [[ "$SINGLE" == "1" ]]; then
  publish_bundles "$candidate_staged_output" "$CANDIDATE_OUTPUT"
  emit_provenance_receipt \
    candidate "$CANDIDATE_OUTPUT" "$candidate_mode" candidate \
    "$candidate_address" "$candidate_report_sha256"
  if [[ "$candidate_mode" == "produced" ]]; then
    cache_store "$candidate_address" "$CANDIDATE_OUTPUT"
  fi
  exit 0
fi

read -r baseline_address baseline_producer baseline_resident baseline_sources baseline_config baseline_repository \
  <<< "$(fingerprint "$BASELINE_ROOT" baseline)"
printf 'LEAN_REPORT_INPUT side=baseline content_address=sha256:%s producer_sha256=%s repository_inspector_sha256=%s lean_sources_sha256=%s lean_config_sha256=%s\n' \
  "$baseline_address" "$baseline_producer" "$baseline_resident" "$baseline_sources" "$baseline_config"

if [[ "$candidate_address" == "$baseline_address" ]]; then
  prepare_reused_bundle \
    "$BASELINE_ROOT" "$BASELINE_OUTPUT" "$candidate_staged_output" \
    "$baseline_address" "$baseline_producer" "$baseline_resident" \
    "$baseline_sources" "$baseline_config" "$baseline_repository" \
    "$candidate_report_sha256"
else
  prepare_bundle \
    baseline "$BASELINE_ROOT" "$BASELINE_OUTPUT" "$baseline_address" \
    "$baseline_producer" "$baseline_resident" "$baseline_sources" \
    "$baseline_config" "$baseline_repository"
fi
baseline_staged_output="$LAST_BUNDLE_OUTPUT"
baseline_report_sha256="$LAST_BUNDLE_SHA256"
baseline_mode="$LAST_BUNDLE_MODE"

publish_bundles \
  "$candidate_staged_output" "$CANDIDATE_OUTPUT" \
  "$baseline_staged_output" "$BASELINE_OUTPUT"
emit_provenance_receipt \
  candidate "$CANDIDATE_OUTPUT" "$candidate_mode" candidate \
  "$candidate_address" "$candidate_report_sha256"
baseline_source_side="baseline"
if [[ "$baseline_mode" == "reused" ]]; then baseline_source_side="candidate"; fi
emit_provenance_receipt \
  baseline "$BASELINE_OUTPUT" "$baseline_mode" "$baseline_source_side" \
  "$baseline_address" "$baseline_report_sha256"
if [[ "$candidate_mode" == "produced" ]]; then
  cache_store "$candidate_address" "$CANDIDATE_OUTPUT"
fi
if [[ "$baseline_mode" == "produced" ]]; then
  cache_store "$baseline_address" "$BASELINE_OUTPUT"
fi
