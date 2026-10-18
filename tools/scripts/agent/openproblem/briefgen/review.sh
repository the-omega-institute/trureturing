#!/bin/bash
# Portable brief orchestration. See the openproblem README for inputs.
set -euo pipefail
BRIEF_ENTRY_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
if [ "${1:-}" = --selftest ]; then
  python3 "$BRIEF_ENTRY_DIR/selftest.py" "${BASH_SOURCE[0]}"
  exit $?
fi
. "$BRIEF_ENTRY_DIR/common.sh"
[ "$#" = 7 ] || op_fail 10 USAGE "review.sh: expected 7 arguments"
set -u
S=$OP_SCRATCH
L=$1; PR=$2; BR=$3; WT=$4; ENV=$5; TG=$6; NYX=$7
op_need gh
op_name "$L"
op_file "$TG"
for b in review-oprc-clarification review-verdict-use-block review-trigger-fields-block review-readonly-block; do op_file "$(op_block "$b.md")"; done
PH=$(cd "$OP_MAIN" && gh pr view $PR --json headRefOid -q .headRefOid) || exit 3
WH=$(git -C "$WT" rev-parse HEAD)
RH=$(git -C "$WT" ls-remote origin "refs/heads/$BR" | cut -f1)
if [ -n "$RH" ] && [ "$RH" != "$PH" ]; then echo "PR_HEAD_LAG pr=$PH remote_branch=$RH (GitHub has not synced the push; wait and rerun)"; exit 6; fi
if [ "$PH" != "$WH" ]; then
  if [ -z "$(git -C "$WT" status --porcelain)" ] && git -C "$WT" merge-base --is-ancestor "$PH" "$WH" 2>/dev/null; then
    LEAN4_GUARDRAILS_BYPASS=1 git -C "$WT" reset -q --keep "$PH" && echo "RESET $WT $WH -> $PH"
  else echo "HEAD_MISMATCH worktree=$WH pr=$PH"; exit 4; fi
fi
cd "$S"
python3 "$OP_OPENPROBLEM_DIR/gen_review.py" "$L" "$PR" "$BR" "$WT" "$ENV" "$TG" "$NYX"
for r in architecture quality tests; do
  cat "$(op_block review-oprc-clarification.md)" >> "$S/briefs/review-$L-$r.md"
  cat "$(op_block review-verdict-use-block.md)" >> "$S/briefs/review-$L-$r.md"
  cat "$(op_block review-trigger-fields-block.md)" >> "$S/briefs/review-$L-$r.md"
  [ "$r" = "$NYX" ] && continue
  cat "$(op_block review-readonly-block.md)" >> "$S/briefs/review-$L-$r.md"
done
grep -c "$PH" "$S/briefs/review-$L-$NYX.md" | sed 's/^/head_mentions=/'
python3 "$OP_BRIEF_DIR/fix_review.py" "$S/briefs/review-$L-architecture.md" "$S/briefs/review-$L-quality.md" "$S/briefs/review-$L-tests.md"
