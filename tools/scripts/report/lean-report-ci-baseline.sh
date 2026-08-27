#!/usr/bin/env bash
set -euo pipefail

export LC_ALL=C

BUNDLE=""
CACHE_ROOT=""
STAGING=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --bundle) BUNDLE="$2"; shift 2 ;;
    --cache-root) CACHE_ROOT="$2"; shift 2 ;;
    *) echo "lean-report-ci-baseline: unknown argument '$1'" >&2; exit 2 ;;
  esac
done

[[ -n "$BUNDLE" && "$BUNDLE" == /* ]] \
  || { echo "lean-report-ci-baseline: --bundle must be absolute" >&2; exit 2; }
[[ -n "$CACHE_ROOT" && "$CACHE_ROOT" == /* ]] \
  || { echo "lean-report-ci-baseline: --cache-root must be absolute" >&2; exit 2; }

fallback() {
  printf 'LEAN_REPORT_CI_BASELINE status=fallback reason=%s\n' "$1" >&2
  exit 0
}

cleanup() {
  [[ -z "$STAGING" ]] || rm -rf -- "$STAGING"
}
trap cleanup EXIT HUP INT TERM

for suffix in '' .sha256 .input.attestation .provenance.json .materials.zip; do
  [[ -s "${BUNDLE}${suffix}" ]] || fallback "missing-bundle-member"
done
[[ -d "${BUNDLE}.logs" \
  && -n "$(find "${BUNDLE}.logs" -type f -print -quit 2>/dev/null)" ]] \
  || fallback "missing-producer-logs"

address="$(python3 - "$BUNDLE" <<'PY'
import hashlib
import json
import pathlib
import re
import sys

report = pathlib.Path(sys.argv[1])
digest = hashlib.sha256(report.read_bytes()).hexdigest()
sidecar = pathlib.Path(str(report) + ".sha256").read_text(encoding="ascii").splitlines()
attestation = pathlib.Path(str(report) + ".input.attestation").read_text(encoding="ascii").splitlines()
provenance = json.loads(
    pathlib.Path(str(report) + ".provenance.json").read_text(encoding="utf-8"))
hex64 = re.compile(r"^[0-9a-f]{64}$")
expected_keys = {
    "schema", "side", "mode", "source_side", "input_address",
    "producer_sha256", "repository_inspector_sha256", "lean_sources_sha256",
    "lean_config_sha256", "report_sha256",
}
address = provenance.get("input_address", "")
if (len(sidecar) != 1
        or sidecar[0] != digest + "  raw-lean-report.json"
        or len(attestation) != 4
        or attestation[0] != "schema=stratalint-lean-report-input-attestation-v1"
        or not re.fullmatch(r"repository_input_sha256=[0-9a-f]{64}", attestation[1])
        or attestation[2] != "producer_sha256=" + provenance.get("producer_sha256", "")
        or attestation[3] != "report_sha256=" + digest
        or set(provenance) != expected_keys
        or provenance.get("schema") != "stratalint-lean-report-provenance-v1"
        or provenance.get("side") != "candidate"
        or provenance.get("mode") not in ("produced", "cached")
        or provenance.get("source_side") != "candidate"
        or not address.startswith("sha256:")
        or not hex64.fullmatch(address[7:])
        or any(not hex64.fullmatch(provenance.get(field, "")) for field in (
            "producer_sha256", "repository_inspector_sha256", "lean_sources_sha256",
            "lean_config_sha256", "report_sha256"))
        or provenance.get("report_sha256") != digest):
    raise SystemExit(1)
print(address[7:])
PY
)" || fallback "invalid-attestation"

mkdir -p "$CACHE_ROOT" 2>/dev/null || fallback "cache-root-unavailable"
chmod 700 "$CACHE_ROOT" 2>/dev/null || fallback "cache-root-untrusted"
entry="$CACHE_ROOT/$address"
[[ ! -e "$entry" ]] || fallback "cache-entry-exists"
STAGING="$(mktemp -d "$CACHE_ROOT/.staging.XXXXXXXX" 2>/dev/null)" \
  || fallback "cache-staging-unavailable"
target="$STAGING/raw-lean-report.json"
for suffix in '' .sha256 .input.attestation .provenance.json .materials.zip; do
  ln "${BUNDLE}${suffix}" "${target}${suffix}" 2>/dev/null \
    || cp "${BUNDLE}${suffix}" "${target}${suffix}" \
    || fallback "bundle-copy-failed"
done
cp -R "${BUNDLE}.logs" "${target}.logs" 2>/dev/null \
  || fallback "log-copy-failed"
mv "$STAGING" "$entry" 2>/dev/null || fallback "cache-publish-failed"
STAGING=""
printf 'LEAN_REPORT_CI_BASELINE status=ready input_address=sha256:%s\n' "$address" >&2
printf '%s\n' "$CACHE_ROOT"
