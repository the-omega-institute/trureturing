#!/usr/bin/env bash
# op-ingest-new-noalign.sh — fresh branch from origin/dev + pure append of ADDENDUM to VOLUME + commit, then the
# no-align ingest path (op-ingest-noalign.sh: lean-report → make ingest BASE=<dev sha> → verify atoms → push → PR).
# Reason: `make align-digestion-status` reorders a foreign entry's coverage_gids and makes `make ingest` fail-closed
# (issue #5606); the append + ingest alone succeeded (PR #5607).
# usage: op-ingest-new-noalign.sh WORKTREE NEW_BRANCH ADDENDUM_MD SUBJ_FILE PRMSG_FILE PATTERN [VOLUME_RELPATH]
# sentinel: forwarded NOALIGN_INGEST_OK pr=<n> / *_FAIL …
set -uo pipefail
WT="${1:?worktree}"; BR="${2:?new branch}"; ADD="${3:?addendum}"; SUBJ="${4:?subject file}"; MSG="${5:?pr message file}"; PAT="${6:?pattern}"; VOL="${7:-docs/develop/theory/PZG_BEDC.md}"
SP="$(cd "$(dirname "$0")" && pwd)"
cd "$WT" || { echo "INGEST_FAIL no-worktree"; exit 3; }
[ -z "$(git status --porcelain)" ] || { echo "INGEST_FAIL dirty-tree"; git status --porcelain | head -5; exit 3; }
git fetch -q origin || { echo "INGEST_FAIL fetch"; exit 3; }
if git show-ref --verify --quiet "refs/heads/$BR"; then echo "INGEST_FAIL branch-exists $BR"; exit 3; fi
git switch -q -c "$BR" origin/dev || { echo "INGEST_FAIL switch"; exit 3; }
echo "BRANCH $BR at $(git rev-parse --short HEAD)"
BASE=$(mktemp); git show origin/dev:"$VOL" > "$BASE"
cmp -s "$BASE" "$VOL" || { echo "INGEST_FAIL volume-differs-from-dev"; exit 3; }
cat "$ADD" >> "$VOL"
head -c "$(wc -c < "$BASE")" "$VOL" | cmp -s - "$BASE" || { echo "INGEST_FAIL prefix-broken"; exit 3; }
git add "$VOL"; git commit -q -F "$SUBJ" || { echo "INGEST_FAIL commit"; exit 3; }
echo "APPENDED $(git rev-parse --short HEAD)"
bash "$SP/op-ingest-noalign.sh" "$WT" "$BR" "$MSG" "$PAT"
echo "INGEST_EXIT=$?"
