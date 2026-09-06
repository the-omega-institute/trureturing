#!/usr/bin/env bash
# op-governance-pr.sh — commit the working-tree change in a governance worktree, push its branch, open the PR
# (optionally auto-merge) and wait for the required checks. usage: op-governance-pr.sh WORKTREE BRANCH COMMIT_MSG_FILE PR_MSG_FILE [AUTO_MERGE=0|1]
# sentinel: GOV_PR_OK pr=<n> head=<sha> / GOV_FAIL <reason>
set -uo pipefail
WT="${1:?worktree}"; BR="${2:?branch}"; CMSG="${3:?commit message file}"; PMSG="${4:?pr message file}"; AUTO="${5:-0}"
cd "$WT" || { echo "GOV_FAIL no-worktree"; exit 3; }
eval "$(sed -n '/^export PATH=/p' tools/scripts/local-harness-gate.sh)"
[ "$(git branch --show-current)" = "$BR" ] || { echo "GOV_FAIL wrong-branch $(git branch --show-current)"; exit 3; }
[ -n "$(git status --porcelain)" ] || { echo "GOV_FAIL nothing-to-commit"; exit 3; }
git add -A && git commit -q -F "$CMSG" || { echo "GOV_FAIL commit"; exit 3; }
git fetch -q origin && git merge -q --no-edit origin/dev || { echo "GOV_FAIL merge-dev"; exit 3; }
git push -q -u origin "$BR" || { echo "GOV_FAIL push"; exit 4; }
LOG=$(mktemp)
if [ "$AUTO" = "1" ]; then make pr-open HEAD="$BR" MESSAGE="$PMSG" AUTO_MERGE=1 2>&1 | tee "$LOG"; else make pr-open HEAD="$BR" MESSAGE="$PMSG" 2>&1 | tee "$LOG"; fi
PR=$(grep -o 'pull/[0-9]*' "$LOG" | head -1 | cut -d/ -f2)
echo "GOV_PR_OK pr=${PR:-unknown} head=$(git rev-parse HEAD)"
