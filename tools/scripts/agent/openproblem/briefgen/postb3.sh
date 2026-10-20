#!/bin/bash
# Wait for required CI, then render three round-one verification briefs.
set -euo pipefail
BRIEF_ENTRY_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
if [ "${1:-}" = --selftest ]; then
  python3 "$BRIEF_ENTRY_DIR/selftest.py" "${BASH_SOURCE[0]}"
  exit $?
fi
. "$BRIEF_ENTRY_DIR/common.sh"
[ "$#" = 2 ] || op_fail 10 USAGE 'postb3.sh LANE PR'
L=$1; PR=$2
op_name "$L"; op_uint PR "$PR"; op_need gh make
op_file "$OP_SCRATCH/lanes/$L.json"
op_file "$OP_SCRATCH/lanes/$L.target.md"
cd "$OP_MAIN"
H=$(gh pr view "$PR" --json headRefOid -q .headRefOid) || op_fail 16 GH_ERROR 'cannot read PR head'
case "$H" in *[!0-9a-f]*|'') op_fail 13 BAD_HEAD "$H";; esac
[ "${#H}" = 40 ] || op_fail 13 BAD_HEAD "$H"
make pr-watch "PR=$PR" "HEAD_SHA=$H" > "$OP_SCRATCH/logs/prwatch-$L-postb.log" 2>&1 || op_fail 16 WATCH_FAILED "$PR"
W=$(grep PR_WATCH_RESULT "$OP_SCRATCH/logs/prwatch-$L-postb.log" | tail -1)
echo "$W"
case "$W" in *outcome=green*) ;; *) op_fail 13 NOT_GREEN "$W";; esac
git fetch -q origin dev "+refs/pull/$PR/head:refs/remotes/pr/$PR"
F=$(python3 - "$OP_SCRATCH" "$L" <<'PY'
import pathlib, re, sys
files = sorted((pathlib.Path(sys.argv[1]) / 'logs').glob('implb-' + sys.argv[2] + '-r*.log'))
flights = [f for p in files for f in re.findall(r'FLIGHT ([0-9a-f]+)', p.read_text())]
if not flights:
    sys.exit(11)
print(flights[-1])
PY
)
RJ=$(op_latest_result "$F")
[ "$RJ" != NO_RESULT ] || op_fail 11 INPUT_MISSING "$F"
WT=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["worktree"])' "$OP_SCRATCH/lanes/$L.json")
BR=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["branch"])' "$OP_SCRATCH/lanes/$L.json")
python3 "$OP_OPENPROBLEM_DIR/gen_review.py" --codex3 "$L" "$PR" "$BR" "$WT" "$RJ" "$OP_SCRATCH/lanes/$L.target.md" 1 > "$OP_SCRATCH/logs/genreview-$L.log" 2>&1
cat "$OP_SCRATCH/logs/genreview-$L.log"
for role in architecture quality tests; do
  file="$OP_SCRATCH/briefs/review-$L-$role-r1.md"
  op_file "$file"
  size=$(wc -c < "$file")
  [ "$size" -gt 5000 ] || op_fail 13 NOT_READY "$file size=$size"
done
echo READY
