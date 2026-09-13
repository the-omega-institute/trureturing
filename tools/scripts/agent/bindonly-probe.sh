#!/usr/bin/env bash
# Ask whether a candidate target closes from pinned Mathlib alone, before a seat
# is dispatched to prove it.
#
# The repository's admission rule is that a first freeze needs escape content
# (CLAUDE.md 第 3.2 条): a target the pinned library already closes in one term is
# bind-only and must not get an implementation lane. Finding that out costs a
# seat's whole lifetime when the seat finds it, and about a minute when this
# does. The recorded history is 3 dispatches that came back bind-only.
#
# What it answers is narrow and one-sided: `closed` is decisive — Mathlib alone
# proved it, do not dispatch. `open` is NOT sufficient to dispatch: `exact?`
# searches for a single term, so a two-line library composition still reports
# open, and the probe does no in-repository duplicate search at all. Treat
# `open` as "this one cheap refutation did not fire", nothing more.
#
# Usage: bindonly-probe.sh <lane-dir> <statement-file> [flight-id] [timeout-seconds]
#   statement-file holds the bare target, e.g.
#       theorem probe_target (p : Nat) (hp : p.Prime) : ...
#   with no `:= by` and no imports; the probe supplies both.
# Sentinel: BINDONLY_PROBE status=<closed|open|error> lane=<dir> seconds=<n> probe=<path>
# Exit 0 when the probe ran and the target stayed open, 3 when Mathlib closed it,
# 2 when the probe could not run.
set -u
export LC_ALL=C

fail() { echo "BINDONLY_PROBE status=error lane=${LANE:-none} seconds=0 probe=none reason=$1"; exit 2; }

LANE="${1:?usage: bindonly-probe.sh <lane-dir> <statement-file> [flight-id] [timeout-seconds]}"
STMT="${2:?usage: bindonly-probe.sh <lane-dir> <statement-file> [flight-id] [timeout-seconds]}"
FLIGHT="${3:-probe-$$}"
BUDGET="${4:-600}"

[ -d "$LANE" ] || fail "lane-not-a-directory"
[ -f "$LANE/lakefile.toml" ] || fail "lane-has-no-lakefile"
[ -f "$STMT" ] || fail "statement-file-missing"
[ -s "$STMT" ] || fail "statement-file-empty"
grep -q '^[[:space:]]*theorem[[:space:]]' "$STMT" || fail "statement-file-has-no-theorem"
grep -q ':=' "$STMT" && fail "statement-file-carries-a-proof"
case "$FLIGHT" in *[!A-Za-z0-9._-]*) fail "flight-id-not-plain" ;; esac
case "$BUDGET" in ''|*[!0-9]*) fail "timeout-not-a-number" ;; esac

# The probe file lives in the lane, not /tmp: concurrent seats collide on /tmp
# names, and a lane-local file is still there when the reading is questioned. It
# goes under .lake, which git ignores, so a later `git add -A` in that lane
# cannot sweep a probe into a commit.
probe_dir="$LANE/.lake/bindonly-probe"
mkdir -p "$probe_dir" || fail "cannot-create-probe-dir"
probe="$probe_dir/BindOnlyProbe_$FLIGHT.lean"
{
  echo "import Mathlib"
  echo
  cat "$STMT"
  echo " := by"
  echo "  exact?"
} > "$probe"

# 第 8.3 条: never a bare lake on a cold tree — the first bare command on a tree
# with no stamp forfeits its clonefile donor and buys a full rebuild.
( cd "$LANE" && make lean-cache-ensure ) > "$probe.ensure.log" 2>&1 \
  || { echo "BINDONLY_PROBE status=error lane=$LANE seconds=0 probe=$probe reason=ensure-failed"; exit 2; }

started=$(date +%s)
( cd "$LANE" && timeout "$BUDGET" lake env lean "$probe" ) > "$probe.out" 2>&1
rc=$?
seconds=$(( $(date +%s) - started ))

if [ "$rc" -eq 124 ]; then
  echo "BINDONLY_PROBE status=open lane=$LANE seconds=$seconds probe=$probe reason=timeout budget=$BUDGET"
  exit 0
fi
if [ "$rc" -eq 0 ]; then
  echo "BINDONLY_PROBE status=closed lane=$LANE seconds=$seconds probe=$probe"
  exit 3
fi

# A statement that does not elaborate also exits nonzero, and reporting that as
# `open` would be the exact failure this tool exists to prevent: a typo would
# read as "not bind-only, dispatch a seat". Measured on this tool's own first
# real use — a target written with `List.Sorted`, which this pinned Mathlib
# replaced by `List.SortedLE`, produced both an unknown-field error and an
# `exact?` failure, and the first version called it `open`.
# An unbuilt lane fails the same way a broken statement does, and the two need
# opposite actions: warm the lane, or fix the target. Measured 2026-09-10 — a
# worktree whose cache had not been provisioned reported `unknown module prefix
# 'Mathlib'`, the classifier below called it `statement-did-not-elaborate`, and
# the caller went and rewrote a statement that was never the problem. The
# signature is checked first because it makes every later count meaningless:
# with no Mathlib, nothing in the file elaborates.
if grep -qE "unknown (module prefix|package)" "$probe.out" 2>/dev/null; then
  echo "BINDONLY_PROBE status=error lane=$LANE seconds=$seconds probe=$probe" \
       "reason=mathlib-unavailable-in-lane"
  exit 2
fi

others=$(grep -E 'error(\(|:)' "$probe.out" 2>/dev/null \
  | grep -cv 'could not close the goal' || true)
others=${others:-0}
if [ "$others" -gt 0 ]; then
  echo "BINDONLY_PROBE status=error lane=$LANE seconds=$seconds probe=$probe" \
       "reason=statement-did-not-elaborate errors=$others"
  exit 2
fi

echo "BINDONLY_PROBE status=open lane=$LANE seconds=$seconds probe=$probe exit=$rc"
exit 0
