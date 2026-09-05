#!/usr/bin/env bash
# op-sync-dev.sh — merge origin/dev into a lane branch (merge-only, never rebase) and push, so GitHub recomputes the
# PR merge ref (a plain `gh run rerun` reuses the stale merge ref). Then wait for the three required checks.
# usage: op-sync-dev.sh WORKTREE BRANCH PR   sentinel: SYNC_OK head=<sha> checks=<exit>
set -euo pipefail
WT="${1:?worktree}"; BR="${2:?branch}"; PR="${3:?pr number}"
cd "$WT"
[ "$(git branch --show-current)" = "$BR" ] || { echo "SYNC_FAIL wrong-branch $(git branch --show-current)"; exit 3; }
[ -z "$(git status --porcelain)" ] || { echo "SYNC_FAIL dirty-tree"; exit 3; }
git fetch -q origin
if git merge-base --is-ancestor origin/dev HEAD; then
  echo "SYNC_NOOP already contains origin/dev; creating an empty sync commit is not allowed — nothing pushed"
  exit 0
fi
git merge -q --no-edit origin/dev || { echo "SYNC_FAIL merge-conflict"; git merge --abort; exit 4; }
git push -q origin "$BR"
HEAD=$(git rev-parse HEAD)
echo "PUSHED head=$HEAD"
set +e
gh pr checks "$PR" -R the-omega-institute/trureturing --watch --fail-fast >/dev/null 2>&1; rc=$?
set -e
echo "SYNC_OK head=$HEAD checks=$rc"
gh pr view "$PR" -R the-omega-institute/trureturing --json headRefOid,statusCheckRollup --jq '{head:.headRefOid[0:10],checks:[.statusCheckRollup[]|{n:.name[0:22],c:.conclusion}]}'
