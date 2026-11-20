#!/bin/bash
# List frozen modules without a corresponding Blueprint Scribe.
# Usage: scribe_gap.sh REPO [OUT.txt]
set -euo pipefail
REPO="${1:-}"
[ -n "$REPO" ] || { echo "SCRIBE_GAP_USAGE: scribe_gap.sh REPO [OUT.txt]" >&2; exit 64; }
[ -d "$REPO/.git" ] || [ -f "$REPO/.git" ] || { echo "SCRIBE_GAP_BAD_REPO=$REPO" >&2; exit 65; }
[ -d "$REPO/Golden/Frozen/state" ] || { echo "SCRIBE_GAP_NO_FROZEN_STATE=$REPO" >&2; exit 66; }
[ -d "$REPO/Blueprint" ] || { echo "SCRIBE_GAP_NO_BLUEPRINT=$REPO" >&2; exit 67; }
OUT="${2:-}"
cd "$REPO"
tmp=""
states=""
trap 'rm -f "$tmp" "$states"' EXIT
tmp=$(mktemp)
states=$(mktemp)
if ! find Golden/Frozen/state -name '*.lean.json' > "$states"; then
  echo "SCRIBE_GAP_SCAN_FAILED root=Golden/Frozen/state" >&2
  exit 69
fi
sort -o "$states" "$states"
frozen=0
missing=0
while IFS= read -r state; do
  frozen=$((frozen + 1))
  rel=${state#Golden/Frozen/state/}
  rel=${rel%.lean.json}
  if [ ! -f "Blueprint/$rel.scribe.cs" ]; then
    missing=$((missing + 1))
    printf '%s\n' "$rel" >> "$tmp"
  fi
done < "$states"
[ "$frozen" -gt 0 ] || { echo "SCRIBE_GAP_EMPTY_FROZEN_STATE" >&2; exit 68; }
if [ -n "$OUT" ]; then
  sort -u "$tmp" > "$OUT"
else
  sort -u "$tmp"
fi
echo "SCRIBE_GAP_OK frozen=$frozen missing=$missing"
