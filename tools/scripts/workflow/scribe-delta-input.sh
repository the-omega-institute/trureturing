#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 4 ]]; then
  echo "usage: scribe-delta-input.sh REPOSITORY BASE CHANGES_FILE PRODUCER_PATHS_FILE" >&2
  exit 2
fi

REPOSITORY="$1"
BASE="$2"
CHANGES_FILE="$3"
PRODUCER_PATHS_FILE="$4"
[[ "$REPOSITORY" == /* && -d "$REPOSITORY" ]] \
  || { echo "scribe-delta-input: REPOSITORY must be an absolute directory" >&2; exit 2; }
[[ "$BASE" =~ ^[0-9a-fA-F]{40}$|^[0-9a-fA-F]{64}$ ]] \
  || { echo "scribe-delta-input: BASE must be an exact git object ID" >&2; exit 2; }
[[ "$CHANGES_FILE" == /* && "$PRODUCER_PATHS_FILE" == /* ]] \
  || { echo "scribe-delta-input: output paths must be absolute" >&2; exit 2; }

git -C "$REPOSITORY" cat-file -e "${BASE}^{commit}" \
  || { echo "scribe-delta-input: BASE commit is unavailable" >&2; exit 2; }
TMP_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/stratalint-scribe-delta.XXXXXXXX")"
cleanup() { rm -rf -- "$TMP_ROOT"; }
trap cleanup EXIT

git -C "$REPOSITORY" diff --name-only --no-renames -z "$BASE" -- \
  > "$TMP_ROOT/changes"
git -C "$REPOSITORY" ls-files --others --exclude-standard -z \
  >> "$TMP_ROOT/changes"
"$REPOSITORY/tools/scripts/report/lean-report-input.sh" scribe-producer-paths \
  --repository "$REPOSITORY" > "$TMP_ROOT/producer-paths"

mkdir -p -- "$(dirname "$CHANGES_FILE")" "$(dirname "$PRODUCER_PATHS_FILE")"
mv -- "$TMP_ROOT/changes" "$CHANGES_FILE"
mv -- "$TMP_ROOT/producer-paths" "$PRODUCER_PATHS_FILE"
