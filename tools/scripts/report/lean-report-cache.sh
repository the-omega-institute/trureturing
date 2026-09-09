#!/usr/bin/env bash

report_cache_root() {
  if [[ -n "${STRATALINT_REPORT_CACHE_ROOT:-}" ]]; then
    printf '%s\n' "$STRATALINT_REPORT_CACHE_ROOT"
  elif [[ "${CI:-}" == true || "${CI:-}" == 1 ]]; then
    local report_cache_base="${RUNNER_TEMP:-${TMPDIR:-/tmp}}"
    printf '%s/stratalint-lean-report-cache\n' "${report_cache_base%/}"
  else
    printf '%s/stratalint-lean-report-cache\n' "${XDG_CACHE_HOME:-$HOME/.cache}"
  fi
}
[[ "${BASH_SOURCE[0]}" == "$0" ]] || return 0
set -euo pipefail
export LC_ALL=C
export PYTHONDONTWRITEBYTECODE=1
SCRIPT_DIRECTORY="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
ROOT="$(cd "$SCRIPT_DIRECTORY/../../.." && pwd -P)"
HELPER="$SCRIPT_DIRECTORY/lean-report-cache.py"
INPUT="$SCRIPT_DIRECTORY/lean-report-input.sh"
ADAPTER="$SCRIPT_DIRECTORY/lean-report-ci-baseline.sh"
TAG=lean-report-cache-v1
REPO="${STRATALINT_REPORT_CACHE_REPO:-the-omega-institute/trureturing}"
COMMAND="${1:-}"
[[ $# -gt 0 ]] && shift
BUNDLE=""
OVERRIDES=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --repository) ROOT="$2"; shift 2 ;;
    --bundle) BUNDLE="$2"; shift 2 ;;
    --producer|--inspector) OVERRIDES+=("$1" "$2"); shift 2 ;;
    *) echo "lean-report-cache: unknown argument '$1'" >&2; exit 2 ;;
  esac
done
[[ "$COMMAND" == fetch || "$COMMAND" == publish ]] \
  || { echo 'usage: lean-report-cache.sh fetch|publish [--repository DIR] [--bundle FILE]' >&2; exit 2; }
[[ "$ROOT" == /* && -d "$ROOT" ]] || exit 2
# Bulk IO deadline in integer seconds, separate from the 30-second metadata
# deadline. Bound optional transfers to at most one day; this is not a resource
# estimate or a report correctness budget. An explicitly empty override is bad.
TRANSFER_TIMEOUT_SECONDS="${STRATALINT_REPORT_CACHE_TRANSFER_TIMEOUT_SECONDS-1800}"
MAX_TRANSFER_TIMEOUT_SECONDS=86400
if [[ ! "$TRANSFER_TIMEOUT_SECONDS" =~ ^[1-9][0-9]{0,4}$ ]] \
  || (( TRANSFER_TIMEOUT_SECONDS > MAX_TRANSFER_TIMEOUT_SECONDS )); then
  echo 'lean-report-cache: STRATALINT_REPORT_CACHE_TRANSFER_TIMEOUT_SECONDS must be an integer from 1 to 86400' >&2
  exit 2
fi
CACHE_ROOT="$(report_cache_root)"
[[ "$CACHE_ROOT" == /* ]] || { echo 'lean-report-cache: cache root must be absolute' >&2; exit 2; }
TMP_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/lean-report-cache.XXXXXXXX")"
trap 'rm -rf -- "$TMP_ROOT"' EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

miss() { printf 'LEAN_REPORT_CACHE status=miss reason=%s\n' "$1" >&2; exit 1; }
# Network deadline, not a capacity estimate. Each gh request is bounded; fetch
# reads one container, all paginated asset metadata, then at most two bundles.
gh_io() {
  local timeout=30
  if [[ "$1" == release && ( "$2" == upload || "$2" == download ) ]]; then
    timeout="$TRANSFER_TIMEOUT_SECONDS"
  fi
  python3 - "$timeout" "$(command -v gh)" "$@" <<'PY'
import subprocess
import sys
timeout = int(sys.argv[1])
try:
    raise SystemExit(subprocess.run(sys.argv[2:], timeout=timeout).returncode)
except (OSError, subprocess.TimeoutExpired) as error:
    print(f"lean-report-cache: GitHub unavailable timeout_seconds={timeout}: {error}", file=sys.stderr)
    raise SystemExit(1)
PY
}

tuple="$("$BASH" "$INPUT" address --repository "$ROOT" ${OVERRIDES[@]+"${OVERRIDES[@]}"})" || miss input-unavailable
pattern='^([0-9a-f]{64} ){3}[0-9a-f]{64}$'
[[ "$tuple" =~ $pattern ]] || miss invalid-input
read -r repository producer sources config <<< "$tuple"
coordinates="$("$BASH" "$INPUT" coordinates "$producer" "$producer" "$sources" "$config")" || miss invalid-input
address="${coordinates%% *}"
asset="$(python3 "$HELPER" name "$repository" "$producer" "$producer" "$config")" || miss invalid-input

download_verified() {
  local name="$1" destination="$2"
  # 0 = verified; 1 = rejected contents; 2 = unavailable transport or verifier.
  # Preserve the helper result: failure to verify does not establish corruption.
  mkdir -p "$destination" || return 2
  gh_io release download "$TAG" --repo "$REPO" --dir "$destination" \
    --pattern "$name" --pattern "$name.sha256" || return 2
  python3 "$HELPER" unpack "$destination/$name" "$destination/bundle"
}

if [[ "$COMMAND" == fetch ]]; then
  python3 "$HELPER" root "$CACHE_ROOT" || miss cache-root-unavailable
  if python3 "$HELPER" local-seed "$CACHE_ROOT" "$address" "$producer" "$producer" "$config"; then
    printf 'LEAN_REPORT_CACHE status=hit mode=local-seed\n' >&2
    exit 0
  fi
  release_id="$(gh_io api "repos/$REPO/releases/tags/$TAG" --jq .id)" || miss release-unavailable
  [[ "$release_id" =~ ^[0-9]+$ ]] || miss invalid-release
  gh_io api --paginate --slurp "repos/$REPO/releases/$release_id/assets?per_page=100" > "$TMP_ROOT/assets.json" \
    || miss assets-unavailable
  python3 "$HELPER" select "$TMP_ROOT/assets.json" "$asset" > "$TMP_ROOT/candidates" || miss invalid-assets
  attempt=0
  while IFS= read -r name; do
    attempt=$((attempt + 1))
    destination="$TMP_ROOT/download-$attempt"
    if download_verified "$name" "$destination"; then
      imported="$("$BASH" "$ADAPTER" --bundle "$destination/bundle/raw-lean-report.json" \
        --cache-root "$CACHE_ROOT" --transport)"
      if [[ -n "$imported" && -d "$imported" ]]; then
        mode=seed
        [[ "$name" != "$asset" ]] || mode=exact
        printf 'LEAN_REPORT_CACHE status=hit mode=%s asset=%s\n' "$mode" "$name" >&2
        exit 0
      fi
    fi
    printf 'LEAN_REPORT_CACHE status=miss reason=invalid-or-unavailable-asset asset=%s\n' "$name" >&2
  done < "$TMP_ROOT/candidates"
  miss no-usable-bundle
fi

[[ "$BUNDLE" == /* && -s "$BUNDLE" ]] || { echo 'lean-report-cache: publish requires an absolute bundle' >&2; exit 2; }
"$BASH" "$INPUT" verify --repository "$ROOT" --report "$BUNDLE" ${OVERRIDES[@]+"${OVERRIDES[@]}"}
staged="$("$BASH" "$ADAPTER" --bundle "$BUNDLE" --staging-directory "$TMP_ROOT/staged" --transport)"
[[ -n "$staged" && -s "$staged" ]] || miss invalid-publication-bundle
python3 "$HELPER" pack "$staged" "$TMP_ROOT/$asset"
release_id="$(gh_io api "repos/$REPO/releases/tags/$TAG" --jq .id)" || release_id=""
if [[ -z "$release_id" ]]; then
  commit="${GITHUB_SHA:-$(git -C "$ROOT" rev-parse HEAD)}"
  if ! gh_io release create "$TAG" --repo "$REPO" --target "$commit" --latest=false \
    --title 'Lean report cache v1' --notes 'Optional content-addressed Lean reports; full input and bundle validation is required on reuse.'; then
    release_id="$(gh_io api "repos/$REPO/releases/tags/$TAG" --jq .id)" || miss release-unavailable
    [[ "$release_id" =~ ^[0-9]+$ ]] || miss invalid-release
  fi
fi
upload_options=()
if [[ -n "$release_id" ]]; then
  [[ "$release_id" =~ ^[0-9]+$ ]] || miss invalid-release
  gh_io api --paginate --slurp "repos/$REPO/releases/$release_id/assets?per_page=100" > "$TMP_ROOT/assets.json" \
    || miss publication-unavailable
  state="$(python3 "$HELPER" publication-state "$TMP_ROOT/assets.json" "$asset" "$MAX_TRANSFER_TIMEOUT_SECONDS")" || miss publication-unavailable
  case "$state" in
    complete)
      verification=0
      download_verified "$asset" "$TMP_ROOT/existing" || verification=$?
      case "$verification" in
        0) printf 'LEAN_REPORT_CACHE status=published mode=existing asset=%s\n' "$asset" >&2; exit 0 ;;
        1) upload_options=(--clobber) ;;
        *) miss publication-unavailable ;;
      esac ;;
    starter)
      gh_io api --paginate --slurp "repos/$REPO/releases/$release_id/assets?per_page=100" > "$TMP_ROOT/confirmed-assets.json" \
        || miss publication-unavailable
      python3 "$HELPER" starter-recovery-ids "$TMP_ROOT/assets.json" "$TMP_ROOT/confirmed-assets.json" \
        "$asset" "$MAX_TRANSFER_TIMEOUT_SECONDS" > "$TMP_ROOT/recovery-ids" || miss publication-unavailable
      printf 'LEAN_REPORT_CACHE status=recovering reason=abandoned-starter asset=%s\n' "$asset" >&2
      # At most two observed IDs, then one non-clobber upload. Deleting by ID
      # cannot remove a new same-name asset installed by a concurrent publisher.
      while IFS= read -r asset_id; do
        gh_io api --method DELETE "repos/$REPO/releases/assets/$asset_id" || miss publication-unavailable
      done < "$TMP_ROOT/recovery-ids"
      ;;
    partial) upload_options=(--clobber) ;;
    absent) ;;
    *) miss publication-unavailable ;;
  esac
fi
# Only confirmed partial/corrupt pairs permit replacement. A fresh upload never
# clobbers a concurrent publisher; on conflict verify that winner once. Either
# path requires a complete validated pair before reporting publication success.
mode=uploaded
gh_io release upload "$TAG" "$TMP_ROOT/$asset" "$TMP_ROOT/$asset.sha256" --repo "$REPO" \
  ${upload_options[@]+"${upload_options[@]}"} || mode=existing
verification=0
download_verified "$asset" "$TMP_ROOT/published" || verification=$?
case "$verification" in
  0) ;;
  1) miss publication-incomplete ;;
  *) miss publication-unavailable ;;
esac
printf 'LEAN_REPORT_CACHE status=published mode=%s asset=%s\n' "$mode" "$asset" >&2
