#!/usr/bin/env bash
set -euo pipefail

export LC_ALL=C

BUNDLE=""
CACHE_ROOT=""
STAGING=""
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
BUNDLE_VALIDATOR="$SCRIPT_DIR/lean-report-bundle-lib.sh"

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

[[ -f "$BUNDLE_VALIDATOR" && -r "$BUNDLE_VALIDATOR" ]] \
  || fallback "validator-unavailable"
# shellcheck source=/dev/null
source "$BUNDLE_VALIDATOR" || fallback "validator-unavailable"
declare -F lean_report_bundle_validate >/dev/null || fallback "validator-unavailable"
address="$(lean_report_bundle_validate "$BUNDLE")" || fallback "invalid-attestation"

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
mv "$STAGING" "$entry" 2>/dev/null || fallback "cache-publish-failed"
STAGING=""
printf 'LEAN_REPORT_CI_BASELINE status=ready input_address=sha256:%s\n' "$address" >&2
printf '%s\n' "$CACHE_ROOT"
