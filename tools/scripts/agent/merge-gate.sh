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
# Review and probe seats do not deposit, so they do not block a merge. Only `implementation`.
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
inflight() {
  # shellcheck disable=SC2009  # pgrep -a is not available on macOS; ps is the portable reading.
  ps -Ao args= 2>/dev/null \
    | grep -E '(^|/)(dispatch\.sh|run-codex-worker\.sh) ' \
    | grep -v -E '(^|[[:space:]])grep([[:space:]]|$)' \
    | awk '{ flight=""; stage=""; d=0;
             # The script must be the COMMAND, i.e. field 1 or the argument of an interpreter in
             # field 1.  Matching it anywhere on the line makes the gate fire on any process that
             # merely mentions a dispatcher — an editor, a checker, or the shell that invoked this
             # gate (case 2026-09-17: a verification command line produced a phantom flight).
             if ($1 ~ /(dispatch\.sh|run-codex-worker\.sh)$/) d=1;
             else if (NF>1 && $1 ~ /(^|\/)(bash|zsh|ksh|sh)$/ && $2 ~ /(dispatch\.sh|run-codex-worker\.sh)$/) d=2;
             if (d) {
               if ($d ~ /dispatch\.sh$/) { flight=$(d+1); stage=$(d+5) }
               else for (i=d+1;i<=NF;i++) {
                 if ($i == "--flight-id") flight=$(i+1);
                 else if ($i == "--stage") stage=$(i+1);
               }
             }
             if (flight != "") printf "%s\t%s\n", stage, flight }' \
    | sort -u
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
  parse() { awk '{ flight=""; stage=""; d=0;
             if ($1 ~ /(dispatch\.sh|run-codex-worker\.sh)$/) d=1;
             else if (NF>1 && $1 ~ /(^|\/)(bash|zsh|ksh|sh)$/ && $2 ~ /(dispatch\.sh|run-codex-worker\.sh)$/) d=2;
             if (d) {
               if ($d ~ /dispatch\.sh$/) { flight=$(d+1); stage=$(d+5) }
               else for (i=d+1;i<=NF;i++) {
                 if ($i == "--flight-id") flight=$(i+1);
                 else if ($i == "--stage") stage=$(i+1);
               }
             }
             if (flight != "") printf "%s\t%s\n", stage, flight }'; }
  out=$(echo 'bash tools/scripts/agent/seat/dispatch.sh F1 1 brief.md /tmp/wt implementation 0 2' | parse)
  [ "$out" = "$(printf 'implementation\tF1')" ] || { echo "[FAIL] positional dispatcher shape: got '$out'"; fail=1; }
  out=$(echo 'bash /p/run-codex-worker.sh --flight-id F2 --attempt 1 --stage implementation --work-target /tmp/wt' | parse)
  [ "$out" = "$(printf 'implementation\tF2')" ] || { echo "[FAIL] named-flag runner shape: got '$out'"; fail=1; }
  out=$(echo 'bash /p/run-codex-worker.sh --flight-id F3 --attempt 1 --stage thinking --work-target /tmp/wt' | parse)
  [ "$out" = "$(printf 'thinking\tF3')" ] || { echo "[FAIL] named-flag runner stage: got '$out'"; fail=1; }
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
blockers=$(printf '%s\n' "$rows" | awk -F'\t' '$1=="implementation" && $2!=""{print $2}')

if [ "$MODE" = list ]; then
  if [ -n "${rows//[[:space:]]/}" ]; then
    printf '%s\n' "$rows" | awk -F'\t' '$2!=""{printf "  %-16s %s\n", $1, $2}'
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
