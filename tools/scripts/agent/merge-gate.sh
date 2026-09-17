#!/usr/bin/env bash
# merge-gate.sh — refuse to merge into dev while an implementation seat is running its doors.
#
# WHY THIS EXISTS (case: twice, 2026-09-16 and 2026-09-17). Merging a PR moves `origin/dev`.
# An implementation seat that is between `make lean` and `make deposit*` resolves `BASE=origin/dev`
# WHEN THE DOOR RUNS, so a merge underneath it turns its ancestry predicate false and stops the
# deposit. The stop itself is safe — it writes no frozen state, and the brief template tells the
# seat to fetch, merge, re-verify and continue — but it costs a full rebuild-and-report cycle
# every time, and the orchestrator is the only party who can avoid it.
#
# The first occurrence was answered by teaching the seat to recover (template rule 5'). The second
# occurrence means the seat-side fix was not the root cause: the root cause is that the merging
# side had no check at all. CLAUDE.md 7.11 says the second instance of a symptom is answered by
# fixing the class, so this is the class fix on the merging side.
#
# Review and probe seats do not deposit, so they do not block a merge. Only `implementation` — and
# only the implementation seats that actually reach a door. The two-stage split (README step 5/8,
# gen_stage_briefs.py) gives a Stage-A seat a brief that ends before every door: module, mirror,
# `make lean`/`lean-report`/`emit`, then stop. It never resolves `BASE=origin/dev`, so a merge under
# it costs nothing; blocking on it blocked every merge for the whole hour of every Stage A
# (case 2026-09-17: a merge-ready PR waited on a Stage-A seat that had no door to protect). The
# Stage-A brief is recognised by the name gen_stage_briefs.py writes, `*.stageA.md`, read from the
# dispatcher's positional brief argument; a seat whose brief cannot be read (the runner form carries
# no brief) stays blocking, so the unknown case fails closed.
#
# A Stage-B seat that has ALREADY committed its deposit has nothing left to protect either: after
# the door it only emits, opens the PR and watches CI, and `make pr-open` waits on the remote for
# 10–20 minutes (case 2026-09-18: two merge-ready PRs waited on a seat whose PR #8522 was already
# open). That state is read from the seat's worktree, the dispatcher's positional argument 4: a
# HEAD whose subject starts with `formalize: deposit` is the builder commit the template prescribes
# for the door's delta, so the ancestry predicate has already been evaluated and committed. The
# reading is fail-closed: no worktree on the command line, an unreadable worktree, or any other
# subject keeps the flight blocking. A seat that is still queued at the dispatcher's load gate
# (no codex process yet) STAYS blocking on purpose: it merges `origin/dev` when it starts, and a
# merge landing in the minutes between that merge and its door is exactly the race this gate is
# for — the dispatch has to be withdrawn and re-issued after the window instead.
#
# usage: merge-gate.sh            # exit 0 = no implementation seat in flight; 3 = one is
#        merge-gate.sh --list     # same, and print every in-flight seat with its stage
#        merge-gate.sh --selftest
#
# Exit codes: 0 clear, 2 bad usage, 3 blocked by an in-flight implementation seat.
# It is glue (CLAUDE.md 9.1): it orchestrates pgrep and reads runner state, owns no red/green
# judgement of its own, and carries the three glue obligations — fail-fast on input, a
# distinguishable exit code, and safe re-running.

set -uo pipefail

usage() { printf 'usage: %s [--list|--selftest]\n' "${0##*/}" >&2; exit 2; }

MODE=check
case "${1-}" in
  "")           MODE=check ;;
  --list)       MODE=list ;;
  --selftest)   MODE=selftest ;;
  *)            usage ;;
esac
[ "$#" -le 1 ] || usage

# Every running dispatch.sh names its stage as positional argument 5:
#   dispatch.sh FLIGHT_ID ATTEMPT BRIEF WORKTREE STAGE [STAGGER] [MAX_CODEX]
# Reading the stage from the live command line is the direct reading; the runner's status.json is
# only written at terminal, so it cannot answer "is one running right now" (case: runner artifacts
# appear only at terminal).
# Two dispatchers put seats on this repository and the reading must cover both, or the gate is a
# green that cannot go red (case 2026-09-17: two seats were live as run-codex-worker.sh and
# `--list` printed "no seat in flight").
#   seat/dispatch.sh FLIGHT_ID ATTEMPT BRIEF WORKTREE STAGE ...   (positional, stage is arg 5)
#   run-codex-worker.sh --flight-id F --attempt N --stage S ...   (the sshx plugin runner, named)
# Both are read from the live command line for the same reason: the runner's status.json exists
# only at terminal, so it cannot answer "is one running right now".
# One parser for both the live reading and the selftest, so the test cannot pass on a copy of the
# program while the live program has drifted (mutation on 2026-09-17: a selftest carrying its own
# copy of this awk stayed green after the live copy lost the Stage-A mark).
parse_rows() {
  awk '{ flight=""; stage=""; d=0;
             # The script must be the COMMAND, i.e. field 1 or the argument of an interpreter in
             # field 1.  Matching it anywhere on the line makes the gate fire on any process that
             # merely mentions a dispatcher — an editor, a checker, or the shell that invoked this
             # gate (case 2026-09-17: a verification command line produced a phantom flight).
             if ($1 ~ /(dispatch\.sh|run-codex-worker\.sh)$/) d=1;
             else if (NF>1 && $1 ~ /(^|\/)(bash|zsh|ksh|sh)$/ && $2 ~ /(dispatch\.sh|run-codex-worker\.sh)$/) d=2;
             kind="";
             if (d) {
               if ($d ~ /dispatch\.sh$/) { flight=$(d+1); stage=$(d+5); wt=$(d+4);
                 if ($(d+3) ~ /\.stageA\.md$/) kind="stageA" }
               else for (i=d+1;i<=NF;i++) {
                 if ($i == "--flight-id") flight=$(i+1);
                 else if ($i == "--stage") stage=$(i+1);
                 else if ($i == "--work-target") wt=$(i+1);
               }
             }
             if (flight != "") printf "%s\t%s\t%s\t%s\n", stage, flight, kind, wt; wt="" }'
}

# A row whose worktree HEAD subject starts with `formalize: deposit` gets kind=deposited: the door
# has run and its delta is committed. Read from the worktree, never from the command line, so a
# brief or flight name cannot claim it. Anything unreadable leaves the row as it was (fail closed).
mark_deposited() {
  # Split by hand: a tab is IFS whitespace, so `read` would collapse the empty kind column into
  # the worktree column (mutation 2026-09-18: every deposited case read the path as the kind).
  local line stage flight kind wt rest
  while IFS= read -r line; do
    stage=${line%%$'\t'*}; rest=${line#*$'\t'}
    flight=${rest%%$'\t'*}; rest=${rest#*$'\t'}
    kind=${rest%%$'\t'*}; wt=${rest#*$'\t'}
    [ "$rest" = "$kind" ] && wt=""
    [ -n "$flight" ] || continue
    if [ "$stage" = implementation ] && [ -z "$kind" ] && [ -n "$wt" ] && [ -d "$wt" ]; then
      subj=$(git -C "$wt" log -1 --format=%s 2>/dev/null || true)
      case "$subj" in
        ("formalize: deposit "*) kind=deposited ;;
      esac
    fi
    printf '%s\t%s\t%s\t%s\n' "$stage" "$flight" "$kind" "$wt"
  done
}

inflight() {
  # shellcheck disable=SC2009  # pgrep -a is not available on macOS; ps is the portable reading.
  ps -Ao args= 2>/dev/null \
    | grep -E '(^|/)(dispatch\.sh|run-codex-worker\.sh) ' \
    | grep -v -E '(^|[[:space:]])grep([[:space:]]|$)' \
    | parse_rows \
    | mark_deposited \
    | sort -u
}

# Rows are (stage, flight, kind, worktree). A flight is exempt when any of its rows carries
# kind=stageA (no door in its brief) or kind=deposited (its door already committed): the dispatcher
# row has the brief and worktree, the runner row it spawns does not, and both name the same flight.
blocking_flights() {
  awk -F'\t' '$1=="implementation" && $2!="" { seen[$2]=1; if ($3=="stageA" || $3=="deposited") exempt[$2]=1 }
               END { for (f in seen) if (!(f in exempt)) print f }' | sort
}

# A flight can appear on more than one command line at once (a wrapper shell and the script it
# execs both carry the same arguments), so the rows are deduplicated above: the reading is
# "which flights", not "how many processes".


if [ "$MODE" = selftest ]; then
  fail=0
  out=$(printf 'implementation\ts580742-b-x\nreview\ts580742-rev-x\n' \
        | awk -F'\t' '$1=="implementation"{print $2}')
  [ "$out" = "s580742-b-x" ] || { echo "[FAIL] implementation rows are not selected"; fail=1; }
  out=$(printf 'review\ts580742-rev-x\nthinking\ts580742-probe-x\n' \
        | awk -F'\t' '$1=="implementation"{print $2}')
  [ -z "$out" ] || { echo "[FAIL] review/thinking rows must not block"; fail=1; }
  # the two dispatcher shapes, parsed by the same awk program the live reading uses
  parse() { parse_rows; }
  out=$(echo 'bash tools/scripts/agent/seat/dispatch.sh F1 1 brief.md /tmp/wt implementation 0 2' | parse)
  [ "$out" = "$(printf 'implementation\tF1\t\t/tmp/wt')" ] || { echo "[FAIL] positional dispatcher shape: got '$out'"; fail=1; }
  out=$(echo 'bash /p/run-codex-worker.sh --flight-id F2 --attempt 1 --stage implementation --work-target /tmp/wt' | parse)
  [ "$out" = "$(printf 'implementation\tF2\t\t/tmp/wt')" ] || { echo "[FAIL] named-flag runner shape: got '$out'"; fail=1; }
  out=$(echo 'bash /p/run-codex-worker.sh --flight-id F3 --attempt 1 --stage thinking --work-target /tmp/wt' | parse)
  [ "$out" = "$(printf 'thinking\tF3\t\t/tmp/wt')" ] || { echo "[FAIL] named-flag runner stage: got '$out'"; fail=1; }
  # Stage A is read from the dispatcher's brief name; Stage B and the runner form carry no such mark
  out=$(echo 'bash tools/scripts/agent/seat/dispatch.sh F4 1 /s/briefs/impl-op-w1-x.stageA.md /tmp/wt implementation 0 8' | parse)
  [ "$out" = "$(printf 'implementation\tF4\tstageA\t/tmp/wt')" ] || { echo "[FAIL] stageA brief not recognised: got '$out'"; fail=1; }
  out=$(echo 'bash tools/scripts/agent/seat/dispatch.sh F5 1 /s/briefs/impl-op-w1-x.stageB.filled.md /tmp/wt implementation 0 8' | parse)
  [ "$out" = "$(printf 'implementation\tF5\t\t/tmp/wt')" ] || { echo "[FAIL] stageB brief must carry no mark: got '$out'"; fail=1; }
  # deposited is read from the worktree HEAD subject, and only for an unmarked implementation row
  dep=$(mktemp -d); git -C "$dep" init -q .; git -C "$dep" -c user.name=t -c user.email=t@t commit -q --allow-empty -m 'formalize: deposit X (case)'
  out=$(printf 'implementation\tF7\t\t%s\n' "$dep" | mark_deposited)
  [ "$out" = "$(printf 'implementation\tF7\tdeposited\t%s' "$dep")" ] || { echo "[FAIL] deposited HEAD not recognised: got '$out'"; fail=1; }
  git -C "$dep" -c user.name=t -c user.email=t@t commit -q --allow-empty -m 'formalize: prove X (before the door)'
  out=$(printf 'implementation\tF7\t\t%s\n' "$dep" | mark_deposited)
  [ "$out" = "$(printf 'implementation\tF7\t\t%s' "$dep")" ] || { echo "[FAIL] a pre-door HEAD must stay blocking: got '$out'"; fail=1; }
  out=$(printf 'implementation\tF8\t\t%s/missing\n' "$dep" | mark_deposited)
  [ "$out" = "$(printf 'implementation\tF8\t\t%s/missing' "$dep")" ] || { echo "[FAIL] an unreadable worktree must stay blocking: got '$out'"; fail=1; }
  out=$(printf 'implementation\tF8\t\t\n' | mark_deposited)
  [ "$out" = "$(printf 'implementation\tF8\t\t')" ] || { echo "[FAIL] a row without a worktree must stay blocking: got '$out'"; fail=1; }
  rm -rf "$dep"
  # a Stage-A flight seen through both its dispatcher row and its runner row does not block; a lone runner row does
  out=$(printf 'implementation\tF4\tstageA\t/w\nimplementation\tF4\t\t\nimplementation\tF5\t\t/w\nimplementation\tF6\t\t/w\n' | blocking_flights | tr '\n' ' ')
  [ "$out" = "F5 F6 " ] || { echo "[FAIL] blocking set with a Stage-A pair: got '$out'"; fail=1; }
  out=$(printf 'implementation\tF7\tdeposited\t/w\nimplementation\tF7\t\t\nimplementation\tF8\t\t/w\n' | blocking_flights | tr '\n' ' ')
  [ "$out" = "F8 " ] || { echo "[FAIL] a deposited flight must not block: got '$out'"; fail=1; }
  out=$(printf 'review\tR1\t\t\nthinking\tP1\t\t\n' | blocking_flights)
  [ -z "$out" ] || { echo "[FAIL] review/thinking rows must not block: got '$out'"; fail=1; }
  # a command line that only MENTIONS a dispatcher is not a seat
  out=$(echo 'vim tools/scripts/agent/seat/dispatch.sh F9 1 b /tmp/wt implementation' | parse)
  [ -z "$out" ] || { echo "[FAIL] a mention must not count as a flight: got '$out'"; fail=1; }
  out=$(echo 'python3 -c print(open("/p/run-codex-worker.sh")) --flight-id F9 --stage implementation' | parse)
  [ -z "$out" ] || { echo "[FAIL] a mention with the flags must not count: got '$out'"; fail=1; }
  "$0" --list >/dev/null 2>&1; rc=$?
  { [ "$rc" -eq 0 ] || [ "$rc" -eq 3 ]; } || { echo "[FAIL] --list exit code $rc is neither 0 nor 3"; fail=1; }
  "$0" --bogus >/dev/null 2>&1; rc=$?
  [ "$rc" -eq 2 ] || { echo "[FAIL] bad usage exit code $rc, expected 2"; fail=1; }
  [ "$fail" -eq 0 ] && echo "MERGE_GATE_SELFTEST=ok"
  exit "$fail"
fi

rows=$(inflight)
blockers=$(printf '%s\n' "$rows" | blocking_flights)

if [ "$MODE" = list ]; then
  if [ -n "${rows//[[:space:]]/}" ]; then
    printf '%s\n' "$rows" | awk -F'\t' '$2!=""{printf "  %-16s %s %s\n", $1, $2, $3}'
  else
    echo "  (no seat in flight)"
  fi
fi

if [ -n "${blockers//[[:space:]]/}" ]; then
  printf 'MERGE_GATE=blocked\n'
  printf '%s\n' "$blockers" | while IFS= read -r f; do [ -n "$f" ] && printf 'MERGE_GATE_BLOCKER=%s\n' "$f"; done
  printf 'Merging now moves origin/dev under that seat and stops its deposit at the ancestry check.\n' >&2
  exit 3
fi

printf 'MERGE_GATE=clear\n'
exit 0
