#!/usr/bin/env bash
# op-fold-anchor-cover.sh — repair a lane branch whose history is  builder → merge(dev) → cover-append  (or a mis-squash of
# those) into  builder' (deposit + all covers) → merge(dev) , then force-with-lease push. Never uses reset --hard.
# usage: op-fold-anchor-cover.sh WORKTREE BRANCH ATOM_ID SOURCE_ID   sentinel: FOLD_OK head=<sha> builder=<sha>
set -euo pipefail
WT="${1:?worktree}"; BR="${2:?branch}"; ATOM="${3:?atom id}"; SRC="${4:?source id e.g. cone-v1}"
cd "$WT"
[ "$(git branch --show-current)" = "$BR" ] || { echo "FOLD_FAIL wrong-branch"; exit 3; }
[ -z "$(git status --porcelain)" ] || { echo "FOLD_FAIL dirty-tree"; exit 3; }
git fetch -q origin
OLDHEAD=$(git rev-parse HEAD)
BUILDER=$(git rev-list --no-merges origin/dev..HEAD | tail -1)
[ -n "$BUILDER" ] || { echo "FOLD_FAIL no-builder-commit"; exit 3; }
OPEN="Meta/Digestion/backfill/$SRC/residual-open/$ATOM.yaml"; CLOSED="Meta/Digestion/backfill/$SRC/absorbed-closed/$ATOM.yaml"
git cat-file -e "$OLDHEAD:$CLOSED" || { echo "FOLD_FAIL closed-entry-missing-at-head"; exit 3; }
MSG=$(git log -1 --format=%B "$BUILDER")
git switch -q --detach "$BUILDER"
[ -f "$OPEN" ] && git rm -q "$OPEN"
mkdir -p "$(dirname "$CLOSED")"; git show "$OLDHEAD:$CLOSED" > "$CLOSED"; git add "$CLOSED"
git commit -q --amend -m "$MSG

(anchor-atom coverage edge folded into the builder commit)"
NEWBUILDER=$(git rev-parse HEAD)
git branch -f "$BR" HEAD; git switch -q "$BR"
git merge -q --no-edit origin/dev || { echo "FOLD_FAIL merge-conflict"; git merge --abort; exit 4; }
# content check: lane surfaces identical to the old head
if [ -n "$(git diff --name-only "$OLDHEAD" HEAD -- D5 Blueprint Golden Meta/Digestion | grep -v -E "^Meta/Digestion/backfill/(rh-|gict|pzg|cone)" | head -3)" ]; then :; fi
LANE_DIFF=$(git diff --name-only "$OLDHEAD" HEAD -- D5 Blueprint Golden | wc -l | tr -d ' ')
echo "lane-surface files differing from old head (should be 0 unless dev advanced): $LANE_DIFF"
git diff --name-only "$OLDHEAD" HEAD -- D5 Blueprint Golden | head -5
for f in "$CLOSED"; do [ -f "$f" ] || { echo "FOLD_FAIL closed entry missing after merge"; exit 5; }; done
[ ! -f "$OPEN" ] || { echo "FOLD_FAIL open entry still present"; exit 5; }
git push -q --force-with-lease origin "$BR"
echo "FOLD_OK head=$(git rev-parse HEAD) builder=$NEWBUILDER nonmerge=$(git rev-list --no-merges --count origin/dev..HEAD)"
