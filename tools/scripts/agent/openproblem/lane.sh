#!/usr/bin/env bash
# One open-problem lane, as a callable pipeline instead of an orchestrator's working memory.
#
# The lane shape is documented in README.md and was executed by hand for eight settled problems before
# this script existed. Everything the hand-execution kept in the operator's head is encoded here: the
# stage tokens dispatch.sh accepts, the flight naming, the attempt numbering, where briefs must be
# generated from, and how to read a verdict back out of a seat envelope. Those are exactly the facts that
# do not survive a session boundary.
#
# usage:
#   lane.sh new      LANE                      create the worktree and print the branch
#   lane.sh probe    LANE BRIEF                dispatch the thinking seat
#   lane.sh build    LANE BRIEF                dispatch the implementation seat
#   lane.sh review   LANE PR TARGET [SEATS]    generate briefs and dispatch review seats (default all 3)
#   lane.sh verdicts LANE                      print the latest verdict of every seat of this lane
#   lane.sh status   LANE                      worktree, branch, remote head, PR and required checks
#
# LANE is the short name; the branch is lane/math/op-<LANE> and the worktree
# /Users/auric/trureturing-op-<LANE> by the repository's own convention, both overridable with
# LANE_BRANCH and LANE_WORKTREE.
#
# Exit codes: 0 success; 2 bad arguments or missing input; 3 a dispatched seat did not start; 4 a
# requested reading is unavailable. A seat that starts is not waited on — dispatch.sh owns the seat's
# whole life and the caller must run it under a host background job (CLAUDE.md §8.6).
set -uo pipefail

die() { printf 'lane: %s\n' "$*" >&2; exit "${2:-2}"; }
note() { printf 'lane: %s\n' "$*" >&2; }

HERE="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(git -C "$HERE" rev-parse --show-toplevel)" || die "not inside a git repository"
DISPATCH="$REPO/tools/scripts/agent/seat/dispatch.sh"
GENREVIEW="$HERE/gen_review.py"
[ -x "$DISPATCH" ] || [ -f "$DISPATCH" ] || die "seat dispatcher not found at $DISPATCH"

# The flight prefix must be unique per session or run directories collide silently.
: "${LANE_FLIGHT_PREFIX:=}"
[ -n "$LANE_FLIGHT_PREFIX" ] || die "set LANE_FLIGHT_PREFIX to a session-unique token (a generic flight name collides: RUN_DIR_COLLISION is silent and fast)"

: "${LANE_SCRATCH:=}"
[ -n "$LANE_SCRATCH" ] || die "set LANE_SCRATCH to the session scratchpad directory (gen_review.py writes briefs/ relative to the working directory, so running it elsewhere drops files into the repository work tree)"

lane_worktree() { printf '%s' "${LANE_WORKTREE:-$HOME/trureturing-op-$1}"; }
lane_branch()   { printf '%s' "${LANE_BRANCH:-lane/math/op-$1}"; }

# The stage vocabulary dispatch.sh accepts. Passing anything else fails fast and silently wastes a turn;
# "probe" and "implementation-seat" are the names humans use and neither is accepted.
stage_token() {
  case "$1" in
    probe|thinking)            printf 'thinking' ;;
    build|implementation)      printf 'implementation' ;;
    review)                    printf 'review' ;;
    termination)               printf 'termination' ;;
    *) die "unknown stage '$1' (thinking|implementation|review|termination)" ;;
  esac
}

runs_root() { printf '%s' "${LANE_RUNS_ROOT:-${TMPDIR:-/tmp}/consensus-rnd/sshx}"; }

# Next attempt number for a flight: one past the highest existing attempt directory, or 1.
next_attempt() {
  local dir; dir="$(runs_root)/$1"
  local n=0 d
  for d in "$dir"/attempt-*; do
    [ -d "$d" ] || continue
    local k="${d##*/attempt-}"
    case "$k" in (*[!0-9]*) continue ;; esac
    [ "$k" -gt "$n" ] && n="$k"
  done
  printf '%d' $(( n + 1 ))
}

verdict_of() {  # flight -> "attempt-N verdict" of the latest attempt carrying a result.json
  local dir; dir="$(runs_root)/$1"
  local best="" d
  for d in "$dir"/attempt-*; do
    [ -f "$d/result.json" ] && best="$d"
  done
  [ -n "$best" ] || { printf 'none -\n'; return 0; }
  local v
  v="$(python3 - "$best/result.json" <<'PY'
import json,sys
try:
    c=json.load(open(sys.argv[1])).get('conclusion',{})
    # Seats do not all report the same field: review seats use "verdict", probes add
    # "mathematical_verdict", and the implementation seat reports "status" instead. Reading only
    # "verdict" prints "?" for every completed implementation seat, which reads as a failure.
    print(c.get('verdict') or c.get('mathematical_verdict') or c.get('status') or '?')
except Exception as exc:
    print('UNREADABLE')
PY
)"
  printf '%s %s\n' "$(basename "$best")" "$v"
}

dispatch_seat() {  # flight stage brief worktree
  local flight="$1" stage="$2" brief="$3" wt="$4"
  [ -f "$brief" ] || die "brief not found: $brief"
  [ -d "$wt" ] || die "worktree not found: $wt"
  local attempt; attempt="$(next_attempt "$flight")"
  note "dispatching $flight attempt $attempt stage=$stage worktree=$wt"
  bash "$DISPATCH" "$flight" "$attempt" "$brief" "$wt" "$stage" 0 10
  local rc=$?
  [ "$rc" -eq 0 ] || die "dispatch.sh exited $rc for $flight attempt $attempt" 3
}

cmd="${1:-}"; shift || true
case "$cmd" in
  new)
    lane="${1:-}"; [ -n "$lane" ] || die "usage: lane.sh new LANE"
    wt="$(lane_worktree "$lane")"
    if [ -d "$wt" ]; then note "worktree already present: $wt"; else
      make -C "$REPO" worktree KIND=math NAME="op-$lane" || die "make worktree failed" 3
    fi
    printf '%s\t%s\n' "$(lane_branch "$lane")" "$wt"
    ;;
  probe|build)
    lane="${1:-}"; brief="${2:-}"
    [ -n "$lane" ] && [ -n "$brief" ] || die "usage: lane.sh $cmd LANE BRIEF"
    dispatch_seat "$LANE_FLIGHT_PREFIX-$( [ "$cmd" = probe ] && printf 'probe' || printf 'b')-$lane" \
                  "$(stage_token "$cmd")" "$brief" "$(lane_worktree "$lane")"
    ;;
  review)
    lane="${1:-}"; pr="${2:-}"; target="${3:-}"; seats="${4:-arch qual tests}"
    [ -n "$lane" ] && [ -n "$pr" ] && [ -n "$target" ] || die "usage: lane.sh review LANE PR TARGET [SEATS]"
    [ -f "$target" ] || die "target file not found: $target"
    [ -d "$LANE_SCRATCH" ] || die "LANE_SCRATCH is not a directory: $LANE_SCRATCH"
    ( cd "$LANE_SCRATCH" && python3 "$GENREVIEW" "$lane" "$pr" "$(lane_branch "$lane")" \
        "$(lane_worktree "$lane")" none "$target" architecture ) || die "gen_review.py failed" 3
    for seat in $seats; do
      case "$seat" in
        arch)  b="$LANE_SCRATCH/briefs/review-$lane-architecture.md" ;;
        qual)  b="$LANE_SCRATCH/briefs/review-$lane-quality.md" ;;
        tests) b="$LANE_SCRATCH/briefs/review-$lane-tests.md" ;;
        *) die "unknown seat '$seat' (arch|qual|tests)" ;;
      esac
      # Each seat gets its own worktree; sharing one is a known failure (seats must not share a build tree).
      swt="${LANE_REV_WORKTREE_PREFIX:-$HOME/trureturing-rev-$lane}-$seat"
      [ -d "$swt" ] || die "review worktree missing: $swt (create it detached at the delivered head first)" 4
      dispatch_seat "$LANE_FLIGHT_PREFIX-rev-$lane-$seat" review "$b" "$swt"
    done
    ;;
  verdicts)
    lane="${1:-}"; [ -n "$lane" ] || die "usage: lane.sh verdicts LANE"
    for f in "$LANE_FLIGHT_PREFIX-probe-$lane" "$LANE_FLIGHT_PREFIX-b-$lane" \
             "$LANE_FLIGHT_PREFIX-rev-$lane-arch" "$LANE_FLIGHT_PREFIX-rev-$lane-qual" \
             "$LANE_FLIGHT_PREFIX-rev-$lane-tests"; do
      printf '%-44s %s\n' "${f#$LANE_FLIGHT_PREFIX-}" "$(verdict_of "$f")"
    done
    ;;
  status)
    lane="${1:-}"; [ -n "$lane" ] || die "usage: lane.sh status LANE"
    wt="$(lane_worktree "$lane")"; br="$(lane_branch "$lane")"
    printf 'lane           %s\nbranch         %s\nworktree       %s\n' "$lane" "$br" "$wt"
    if [ -d "$wt" ]; then
      printf 'head           %s\nclean          %s\n' \
        "$(git -C "$wt" rev-parse HEAD 2>/dev/null)" \
        "$([ -z "$(git -C "$wt" status --porcelain 2>/dev/null)" ] && echo yes || echo no)"
    else
      printf 'head           (no worktree)\n'
    fi
    printf 'remote         %s\n' "$(git -C "$REPO" ls-remote origin "$br" 2>/dev/null | cut -f1)"
    if command -v gh >/dev/null 2>&1; then
      gh pr list --head "$br" --json number,isDraft,state,statusCheckRollup \
        --jq '.[] | "pr             #\(.number) draft=\(.isDraft) \(.state)\nchecks         [\([.statusCheckRollup[]? | (.conclusion // .state)] | join(","))]"' 2>/dev/null \
        || printf 'pr             (gh query unavailable)\n'
    fi
    ;;
  ""|-h|--help|help)
    sed -n '2,32p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
    ;;
  *) die "unknown command '$cmd' (new|probe|build|review|verdicts|status)" ;;
esac
