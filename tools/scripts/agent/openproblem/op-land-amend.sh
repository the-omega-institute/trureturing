#!/bin/bash
# op-land-amend.sh <worktree>
#
# Re-emit and amend the deposit commit after a PROSE-ONLY fix (Scribe wording, dossier text,
# library note). It re-emits twice, runs the Scribe corpus test and the header check, then
# amends the existing commit. The branch must not have been pushed.
#
# It refuses when any Lean source is modified. A change to the declaration set invalidates
# the Lean report that the frozen state pin was computed against, so emitting alone cannot
# repair it and the amend would carry a stale pin; the full chain in op-land.sh must run
# instead. The guard exists because that mistake was made once and was caught only by the
# emit step returning 2.
set -u
export PATH="$HOME/.elan/bin:$HOME/.dotnet:/opt/homebrew/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin"

WT="${1:?worktree path}"
cd "$WT" || { echo "AMEND_FAIL_CD $WT"; exit 9; }
echo "AMEND_START=$(date +%T) HEAD0=$(git rev-parse --short HEAD)"

LEAN_DIRTY=$(git status --porcelain -- '*.lean' | head -20)
if [ -n "$LEAN_DIRTY" ]; then
  echo "AMEND_REFUSED_LEAN_CHANGED"
  printf '%s\n' "$LEAN_DIRTY"
  echo "A Lean source changed, so the declaration set may have changed and the frozen state"
  echo "pin is no longer bound to this tree. Run op-land.sh instead."
  exit 6
fi

git status --short

make emit > /tmp/op-amend-emit1-$$.log 2>&1; E1=$?
echo "EMIT1_EXIT=$E1"
grep -E "describe red" /tmp/op-amend-emit1-$$.log | head -5 | cut -c1-300
[ "$E1" -eq 0 ] || { echo "AMEND_ABORT_EMIT log=/tmp/op-amend-emit1-$$.log"; exit 5; }

make emit > /tmp/op-amend-emit2-$$.log 2>&1; E2=$?
echo "EMIT2_EXIT=$E2"
[ "$E2" -eq 0 ] || { echo "AMEND_ABORT_EMIT2"; exit 5; }

dotnet test tools/tests/StrataLint.Scribe.Tests/StrataLint.Scribe.Tests.csproj \
  --configuration Release --filter FullyQualifiedName~FormulaCorpusInventoryTests \
  > /tmp/op-amend-scribe-$$.log 2>&1
echo "SCRIBE_TEST_EXIT=$?"
grep -E "Passed!|Failed!" /tmp/op-amend-scribe-$$.log | tail -1

git add -A
git commit -q --amend --no-edit
echo "AMEND_EXIT=$? HEAD=$(git rev-parse HEAD)"
git show --stat --format='%h %s' HEAD | tail -9

EVENT=$(git show --name-only --format='' HEAD | grep '^Golden/Frozen/accepted/' | head -1)
if [ -n "$EVENT" ]; then
  python3 -c "
import json,sys
d=json.load(open(sys.argv[1]))
print('EVENT_HASH='+str(d.get('event_hash')))
p=d.get('payload',d)
print('STATEMENT_ID='+str(p.get('statement_id')))
" "$EVENT"
fi
echo "AMEND_END=$(date +%T)"
