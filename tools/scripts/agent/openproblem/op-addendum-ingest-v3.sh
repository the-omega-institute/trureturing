#!/usr/bin/env bash
# op-addendum-ingest-v3.sh — append addendum (pure append on dev bytes), then loop {merge origin/dev → lean-report → align-digestion-status → ingest} up to MAXTRY
# times (dev advances hourly; "Lean report input closure changed" / "planned rewrite" both mean: re-align on the newest dev and retry immediately),
# verify the addendum's atoms exist, push, open AUTO_MERGE PR.
# usage: op-addendum-ingest-v3.sh WORKTREE VOLUME_RELPATH ADDENDUM_MD COMMIT_SUBJECT_FILE PR_MSGFILE PATTERN [MAXTRY=3]   sentinel: ADDENDUM_INGEST_OK pr=<n>
set -euo pipefail
WT="${1:?worktree}"; VOL="${2:?volume relpath}"; ADD="${3:?addendum md}"; SUBJ="${4:?commit subject file}"; MSG="${5:?pr message file}"; PAT="${6:?atom grep pattern}"; MAXTRY="${7:-3}"
cd "$WT"
eval "$(sed -n '/^export PATH=/p' tools/scripts/local-harness-gate.sh)"
git fetch -q origin
git merge --ff-only origin/dev >/dev/null 2>&1 || { echo "ADDENDUM_FAIL not-ff-to-dev"; exit 3; }
[ -z "$(git status --porcelain)" ] || { echo "ADDENDUM_FAIL dirty-tree"; exit 3; }
BASE=$(mktemp); git show origin/dev:"$VOL" > "$BASE"
cmp -s "$BASE" "$VOL" || { echo "ADDENDUM_FAIL volume-differs-from-dev"; exit 3; }
cat "$ADD" >> "$VOL"
head -c "$(wc -c < "$BASE")" "$VOL" | cmp -s - "$BASE" || { echo "ADDENDUM_FAIL prefix-broken"; exit 3; }
git add "$VOL"; git commit -q -F "$SUBJ"
THEORY_COMMIT=$(git rev-parse HEAD)
ok=0
for try in $(seq 1 "$MAXTRY"); do
  echo "INGEST_TRY $try"
  git fetch -q origin
  git merge -q --no-edit origin/dev || { echo "ADDENDUM_FAIL merge-conflict"; exit 3; }
  DEVSHA=$(git rev-parse origin/dev); echo "PINNED_BASE $DEVSHA"
  set +e
  make lean-report; rc=$?; [ "$rc" -eq 0 ] || { echo "ADDENDUM_FAIL lean-report rc=$rc"; exit 4; }
  make align-digestion-status BASE="$DEVSHA"; rc=$?
  set -e
  if [ "$rc" -eq 0 ]; then git add -A Meta/Digestion; git commit -q -m "digestion: align truth status before addendum ingest (try $try)" || true; else echo "ALIGN_RC $rc (continuing to ingest)"; fi
  set +e
  make ingest BASE="$DEVSHA"; rc=$?
  set -e
  if [ "$rc" -eq 0 ]; then ok=1; break; fi
  echo "INGEST_RC $rc on try $try"
done
[ "$ok" -eq 1 ] || { echo "ADDENDUM_FAIL ingest exhausted after $MAXTRY tries"; exit 4; }
git add -A Meta/Digestion; git commit -q -m "digestion: ingest addendum atoms ($(basename "$VOL"))" || true
hits=0
for f in $(git diff --name-only "$THEORY_COMMIT" HEAD -- Meta/Digestion | grep residual-open); do
  id=$(basename "$f" .yaml)
  if grep -q -E "$PAT" "Meta/Digestion/atoms/sha256/$id" 2>/dev/null; then hits=$((hits+1)); echo "ATOM_HIT $id"; fi
done
[ "$hits" -gt 0 ] || { echo "ADDENDUM_FAIL no-atom-matched pattern=$PAT (not pushed)"; exit 5; }
BR=$(git branch --show-current)
git push -q -u origin "$BR"
LOG=$(mktemp)
set +e
make pr-open HEAD="$BR" MESSAGE="$MSG" AUTO_MERGE=1 2>&1 | tee "$LOG"
set -e
PR=$(grep -o 'pull/[0-9]*' "$LOG" | head -1 | cut -d/ -f2)
echo "ADDENDUM_INGEST_OK pr=${PR:-unknown} branch=$BR hits=$hits"
