#!/bin/bash
# Usage: gptpro-search.sh ID TRACK [WINDOW]. Search blocks are explicit file inputs.
set -uo pipefail
. "$(dirname "$0")/common.sh"
[ "${1:-}" != --selftest ] || { op_selftest gptpro-search; exit $?; }
[ "$#" -ge 2 ] && [ "$#" -le 3 ] || op_fail 10 USAGE 'gptpro-search.sh ID TRACK [WINDOW]'
op_init; op_scratch; op_need gh
ID=$1; track=$2; window=${3:-}
op_name "$ID"
case "$track" in quick|deep) ;; *) op_fail 13 INVALID_INPUT 'TRACK must be quick or deep';; esac
[ "$track" = quick ] || [ -z "$window" ] || op_fail 13 INVALID_INPUT 'WINDOW applies only to quick'
[ -z "$window" ] || [[ "$window" =~ ^[0-9]{4}(-[0-9]{4})?$ ]] || op_fail 13 INVALID_INPUT 'WINDOW must be YYMM or YYMM-YYMM'
selection=${OP_SEARCH_SELECTION:-$OP_SCRATCH/briefs/search-selection-block.md}
exclusions=${OP_SEARCH_EXCLUSIONS:-$OP_SCRATCH/briefs/search-exclusions-compact.md}
op_file "$selection"; op_file "$exclusions"
op_file "$OP_REPO/tools/scripts/agent/openproblem/render-search-brief.sh"
op_file "$OP_REPO/tools/scripts/agent/nyx/nyx.py"
B=$OP_SCRATCH/briefs/gptpro-search-$ID.md
O=$OP_SCRATCH/results/gptpro-search-$ID.out
G=$OP_SCRATCH/logs/gptpro-search-$ID
bash "$OP_REPO/tools/scripts/agent/openproblem/render-search-brief.sh" "nyxid-oracle:${OP_NAME_PREFIX}gptpro-search-$ID" "$B" "$track" "$window" || exit $?
{ printf '\n'; cat "$selection"; printf '\n'; cat "$exclusions"; printf '\n'; } >> "$B" || op_fail 16 IO_ERROR brief
echo "BRIEF_BYTES $(wc -c < "$B")"
ask() { op_gptpro_ask "$B" "$O" > "$1" 2>&1; rc=$?; tail -1 "$1"; }
archive() {
  local suffix=$1 f
  mkdir -p "$OP_SCRATCH/results/failed" || op_fail 16 IO_ERROR failed
  for f in "$O" "$O."*; do
    [ -f "$f" ] || continue
    mv "$f" "$OP_SCRATCH/results/failed/${f##*/}.$suffix" || op_fail 16 IO_ERROR archive
  done
}
ask "$G.log"
if [ "$rc" -ne 0 ] && [ ! -s "$O.stream" ] && [ -f "$O.stderr" ] && grep -q 'unexpected EOF during chunk size line' "$O.stderr"; then
  archive try1; echo 'NYX_RETRY transport-eof-empty-stream'; ask "$G.retry.log"
fi
n=0
while [ "$rc" -ne 0 ] && [ "$n" -lt 6 ] && [ -f "$O.stderr" ] && grep -q oracle_quota_exceeded "$O.stderr"; do
  n=$((n+1)); archive "quota$n"
  echo "NYX_RETRY quota-exceeded wait=600 attempt=$n"
  sleep 600
  ask "$G.quota$n.log"
done
if [ "$rc" -eq 0 ]; then echo NYX_OK; else echo NYX_FAIL; fi
exit "$rc"
