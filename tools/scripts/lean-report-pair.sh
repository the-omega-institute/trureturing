#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
INPUT_HELPER="$SCRIPT_DIR/report/lean-report-input.sh"
CACHE_HELPER="$SCRIPT_DIR/../lean-inspector/report_cache.py"
SUPERVISOR="$SCRIPT_DIR/report/report-supervisor.sh"
PRODUCER="" LAKE_BIN="" CANDIDATE_ROOT="" CANDIDATE_OUTPUT=""
while [[ $# -gt 0 ]]; do
  [[ $# -ge 2 ]] || { echo 'lean-report-pair: missing argument value' >&2; exit 2; }
  case "$1" in
    --producer) PRODUCER="$2" ;;
    --lake-bin) LAKE_BIN="$2" ;;
    --candidate-root) CANDIDATE_ROOT="$2" ;;
    --candidate-output) CANDIDATE_OUTPUT="$2" ;;
    *) echo "lean-report-pair: unknown argument '$1'" >&2; exit 2 ;;
  esac
  shift 2
done
[[ "$PRODUCER" == /* && -x "$PRODUCER" ]] \
  || { echo 'lean-report-pair: --producer requires an absolute executable' >&2; exit 2; }
[[ "$LAKE_BIN" == /* && -x "$LAKE_BIN" ]] \
  || { echo 'lean-report-pair: --lake-bin requires an absolute executable' >&2; exit 2; }
[[ -d "$CANDIDATE_ROOT" && "$CANDIDATE_OUTPUT" == /* ]] \
  || { echo 'lean-report-pair: candidate root or absolute output is absent' >&2; exit 2; }
CANDIDATE_ROOT="$(cd "$CANDIDATE_ROOT" && pwd -P)"
INSPECTOR="$(dirname "$PRODUCER")/Inspector.lean"
[[ -f "$INSPECTOR" ]] || { echo 'lean-report-pair: producer Inspector.lean is absent' >&2; exit 2; }

# Keep staging on the candidate filesystem but outside .lake: a cold producer
# must be able to seed or switch the entire cache before creating report output.
STAGING="$(mktemp -d "$CANDIDATE_ROOT/.lean-report-bundle.XXXXXXXX")"
finish() { local rc=$?; trap - EXIT; rm -rf -- "$STAGING"; exit "$rc"; }
trap finish EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
OUTPUT="$STAGING/$(basename "$CANDIDATE_OUTPUT")"
# Current keeps raw phase diagnostics outside both cache replacement and staging
# cleanup. They are not a report bundle and cannot establish successful evidence.
LOG_DIR="${STRATALINT_LEAN_REPORT_LOG_DIR:-$OUTPUT.logs}"
[[ "$LOG_DIR" == /* ]] || { echo 'lean-report-pair: log directory must be absolute' >&2; exit 2; }

address_output="$("$INPUT_HELPER" address --repository "$CANDIDATE_ROOT" --producer "$PRODUCER" --inspector "$INSPECTOR")" || exit 2
address_pattern='^([0-9a-f]{64} ){3}[0-9a-f]{64}$'
[[ "$address_output" =~ $address_pattern ]] || { echo 'lean-report-pair: repository input address is malformed' >&2; exit 2; }
read -r repository_sha256 producer_sha256 sources_sha256 config_sha256 <<< "$address_output"
input_address="$(python3 - "$producer_sha256" "$sources_sha256" "$config_sha256" <<'PY'
import hashlib, sys
producer, sources, config = sys.argv[1:]
value = ("schema=stratalint-lean-report-input-v1\n" + f"producer_sha256={producer}\n"
         + f"repository_inspector_sha256={producer}\n" + f"lean_sources_sha256={sources}\n"
         + f"lean_config_sha256={config}\n")
print(hashlib.sha256(value.encode()).hexdigest())
PY
)"
printf 'LEAN_REPORT_INPUT side=candidate content_address=sha256:%s producer_sha256=%s repository_inspector_sha256=%s lean_sources_sha256=%s lean_config_sha256=%s\n' \
  "$input_address" "$producer_sha256" "$producer_sha256" "$sources_sha256" "$config_sha256"

# Existing local/transported reports are seeds. Import never establishes a verdict.
if [[ -n "${STRATALINT_REPORT_CACHE_ROOT:-}" ]]; then
  python3 "$CACHE_HELPER" store --repository "$CANDIDATE_ROOT" \
    --cache-root "$STRATALINT_REPORT_CACHE_ROOT" --report "$CANDIDATE_OUTPUT" || true
fi

"$SUPERVISOR" --role lean-producer --lean-slot -- \
  env LAKE_BIN="$LAKE_BIN" \
    STRATALINT_REPORT_INPUT_ADDRESS="$input_address" \
    STRATALINT_REPORT_REPOSITORY_SHA256="$repository_sha256" \
    STRATALINT_REPORT_PRODUCER_SHA256="$producer_sha256" \
    STRATALINT_REPORT_RESIDENT_SHA256="$producer_sha256" \
    STRATALINT_REPORT_SOURCES_SHA256="$sources_sha256" \
    STRATALINT_REPORT_CONFIG_SHA256="$config_sha256" \
    "$PRODUCER" --repository "$CANDIDATE_ROOT" --output "$OUTPUT" --log-dir "$LOG_DIR"

if [[ "$LOG_DIR" != "$OUTPUT.logs" ]]; then
  cp -R "$LOG_DIR" "$OUTPUT.logs"
fi

python3 "$CACHE_HELPER" bind --repository "$CANDIDATE_ROOT" --report "$OUTPUT" \
  --input-address "$input_address" --repository-sha "$repository_sha256" \
  --producer-sha "$producer_sha256" --sources-sha "$sources_sha256" --config-sha "$config_sha256"
"$INPUT_HELPER" verify --repository "$CANDIDATE_ROOT" --report "$OUTPUT" \
  --producer "$PRODUCER" --inspector "$INSPECTOR"
python3 "$CACHE_HELPER" publish --repository "$CANDIDATE_ROOT" --report "$OUTPUT" --output "$CANDIDATE_OUTPUT"
printf 'LEAN_REPORT_PROVENANCE side=candidate mode=produced source_side=candidate input_address=sha256:%s attestation=%s\n' \
  "$input_address" "${CANDIDATE_OUTPUT}.provenance.json"
if [[ -n "${STRATALINT_REPORT_CACHE_ROOT:-}" ]]; then
  python3 "$CACHE_HELPER" store --repository "$CANDIDATE_ROOT" \
    --cache-root "$STRATALINT_REPORT_CACHE_ROOT" --report "$CANDIDATE_OUTPUT" || true
fi
