#!/bin/bash
# op-land.sh <worktree> <module-relpath-without-extension> <branch> <title> [trailer-file]
#
# The full landing chain for one open-problem lane: sync the lane onto dev, produce a Lean
# report, freeze the module through ledger-align, emit the Scribe projection twice, run the
# Scribe corpus test and the header check, commit everything as one deposit, and push.
#
# Freezing runs BEFORE emitting because a coverage claim needs a frozen host. Emitting runs
# twice because the first run writes the projection and the second proves it is stable.
#
# The commit trailer is read from <trailer-file> when given, so no session identifier is
# baked into this script.
set -u
export PATH="$HOME/.elan/bin:$HOME/.dotnet:/opt/homebrew/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin"

WT="${1:?worktree path}"; MOD="${2:?module path without .lean}"; BR="${3:?branch}"
TITLE="${4:?commit title}"; TRAILER="${5:-}"
cd "$WT" || { echo "LAND_FAIL_CD $WT"; exit 9; }

# A report run on a worktree of a second clone builds a cache that is never shared with the
# base, and nothing downstream reports the cost. Refuse before producing one.
bash "$(dirname "$0")/op-require-base.sh" "$WT" "${OP_BASE_GIT:-$HOME/Desktop/omega/trureturing/.git}" \
  || { echo "LAND_ABORT_FOREIGN_CLONE"; exit 7; }

PROJECT="tools/StrataLint.Cli/StrataLint.Cli.csproj"
REPORT=".lake/build/stratalint/raw-lean-report.json"
STATE="Golden/Frozen/state/$MOD.lean.json"

echo "LAND_START=$(date +%T) HEAD0=$(git rev-parse --short HEAD) BRANCH=$(git rev-parse --abbrev-ref HEAD)"

git fetch -q origin dev && git merge -q --no-edit origin/dev
echo "MERGE_DEV_EXIT=$? HEAD1=$(git rev-parse --short HEAD) dev=$(git rev-parse --short origin/dev)"
git merge-base --is-ancestor origin/dev HEAD \
  && echo "BASE_IS_ANCESTOR=yes" \
  || { echo "BASE_IS_ANCESTOR=no"; exit 4; }

make lean-report > /tmp/op-land-report-$$.log 2>&1
echo "LEAN_REPORT_EXIT=$?"
ls -la "$REPORT" | cut -c1-120

dotnet run --project "$PROJECT" --configuration Release -- \
  ledger-align --add "$MOD.lean" --candidate-lean-report "$REPORT" > /tmp/op-land-align-$$.log 2>&1
echo "LEDGER_ALIGN_EXIT=$?"
grep -E "selectors_considered|added=|conflicts=|LEDGER" /tmp/op-land-align-$$.log | tail -3 | cut -c1-300

if [ -f "$STATE" ]; then
  echo "FROZEN_STATE=present $(head -c 200 "$STATE")"
else
  echo "FROZEN_STATE=MISSING"; tail -20 /tmp/op-land-align-$$.log; exit 3
fi

dotnet run --project "$PROJECT" --configuration Release -- ledger-frozen --target "$MOD.lean"
echo "LEDGER_FROZEN_EXIT=$?"

make emit > /tmp/op-land-emit1-$$.log 2>&1; E1=$?
echo "EMIT1_EXIT=$E1"
grep -E "describe red|changed" /tmp/op-land-emit1-$$.log | tail -6 | cut -c1-300
[ "$E1" -eq 0 ] || { echo "LAND_ABORT_EMIT log=/tmp/op-land-emit1-$$.log"; exit 5; }

make emit > /tmp/op-land-emit2-$$.log 2>&1; E2=$?
echo "EMIT2_EXIT=$E2"
tail -2 /tmp/op-land-emit2-$$.log | cut -c1-200
[ "$E2" -eq 0 ] || { echo "LAND_ABORT_EMIT2"; exit 5; }

dotnet test tools/tests/StrataLint.Scribe.Tests/StrataLint.Scribe.Tests.csproj \
  --configuration Release --filter FullyQualifiedName~FormulaCorpusInventoryTests \
  > /tmp/op-land-scribe-$$.log 2>&1
echo "SCRIBE_TEST_EXIT=$?"
grep -E "Passed!|Failed!" /tmp/op-land-scribe-$$.log | tail -1

bash tools/scripts/agent/header-check.sh "$MOD.lean"; HDR=$?
echo "HEADER_EXIT=$HDR"
# The header check is a gate, not an announcement. Its own output ends with
# "不要 deposit", and a chain that prints that and commits anyway has turned a
# check into a log line. Refuse before anything is committed.
[ "$HDR" -eq 0 ] || { echo "LAND_ABORT_HEADER"; exit 6; }

git status --short
git add -A
{ printf '%s\n' "$TITLE"; [ -n "$TRAILER" ] && [ -f "$TRAILER" ] && { printf '\n'; cat "$TRAILER"; }; } > /tmp/op-land-msg-$$.txt
git commit -q -F /tmp/op-land-msg-$$.txt
echo "COMMIT_EXIT=$? HEAD=$(git rev-parse HEAD)"
git show --stat --format='%h %s' HEAD | head -20

EVENT=$(git show --name-only --format='' HEAD | grep '^Golden/Frozen/accepted/' | head -1)
echo "ACCEPTED_EVENT=$EVENT"
if [ -n "$EVENT" ]; then
  python3 -c "
import json,sys
d=json.load(open(sys.argv[1]))
print('EVENT_HASH='+str(d.get('event_hash')))
p=d.get('payload',d)
print('STATEMENT_ID='+str(p.get('statement_id')))
" "$EVENT" 2>/dev/null
fi

GIT_TERMINAL_PROMPT=0 git -c credential.helper='!gh auth git-credential' \
  push -u origin "$BR" > /tmp/op-land-push-$$.log 2>&1
echo "PUSH_EXIT=$?"; tail -2 /tmp/op-land-push-$$.log
echo "LAND_END=$(date +%T)"
