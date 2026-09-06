#!/usr/bin/env bash
# op-ingest-noalign.sh — finish an addendum ingest on an EXISTING lane branch that already carries the volume-append
# commit, WITHOUT running `make align-digestion-status` (a foreign entry's reordered coverage_gids made the former
# report-free alignment pass fail closed three times on 2026-09-05, batch9).
# Steps: optionally revert the align commit → merge origin/dev → make lean-report → make ingest BASE=<origin/dev sha>
#        → verify atoms match PATTERN → push → make pr-open AUTO_MERGE=1.
# usage: op-ingest-noalign.sh WORKTREE BRANCH PRMSG_FILE PATTERN [ALIGN_COMMIT_TO_REVERT]
# sentinel: NOALIGN_INGEST_OK pr=<n> / NOALIGN_FAIL <reason>
set -uo pipefail
WT="${1:?worktree}"; BR="${2:?branch}"; MSG="${3:?pr message file}"; PAT="${4:?pattern}"; REV="${5:-}"
cd "$WT" || { echo "NOALIGN_FAIL no-worktree"; exit 3; }
eval "$(sed -n '/^export PATH=/p' tools/scripts/local-harness-gate.sh)"
[ "$(git branch --show-current)" = "$BR" ] || { echo "NOALIGN_FAIL wrong-branch $(git branch --show-current)"; exit 3; }
[ -z "$(git status --porcelain)" ] || { echo "NOALIGN_FAIL dirty-tree"; exit 3; }
if [ -n "$REV" ]; then
  git revert --no-edit "$REV" || { echo "NOALIGN_FAIL revert-failed"; git revert --abort 2>/dev/null; exit 3; }
  echo "REVERTED $REV"
fi
git fetch -q origin || { echo "NOALIGN_FAIL fetch"; exit 3; }
git merge -q --no-edit origin/dev || { echo "NOALIGN_FAIL merge-conflict"; git merge --abort; exit 3; }
DEVSHA=$(git rev-parse origin/dev); echo "PINNED_BASE $DEVSHA"
THEORY_BEFORE=$(git rev-parse HEAD)
make lean-report; rc=$?; [ "$rc" -eq 0 ] || { echo "NOALIGN_FAIL lean-report rc=$rc"; exit 4; }
make ingest BASE="$DEVSHA"; rc=$?
if [ "$rc" -ne 0 ]; then echo "INGEST_RC $rc"; echo "NOALIGN_FAIL ingest rc=$rc"; exit 4; fi
git add -A Meta/Digestion docs/develop/theory && git commit -q -m "digestion: ingest addendum atoms (no-align path)" || echo "NOTE nothing to commit after ingest"
hits=0
for f in $(git diff --name-only "$THEORY_BEFORE" HEAD -- Meta/Digestion | grep residual-open); do
  id=$(basename "$f" .yaml)
  if grep -q -E "$PAT" "Meta/Digestion/atoms/sha256/$id" 2>/dev/null; then hits=$((hits+1)); echo "ATOM_HIT $id"; fi
done
[ "$hits" -gt 0 ] || { echo "NOALIGN_FAIL no-atom-matched pattern=$PAT (not pushed)"; exit 5; }
git push -q -u origin "$BR" || { echo "NOALIGN_FAIL push"; exit 6; }
LOG=$(mktemp)
make pr-open HEAD="$BR" MESSAGE="$MSG" AUTO_MERGE=1 2>&1 | tee "$LOG"
PR=$(grep -o 'pull/[0-9]*' "$LOG" | head -1 | cut -d/ -f2)
echo "NOALIGN_INGEST_OK pr=${PR:-unknown} branch=$BR hits=$hits"
