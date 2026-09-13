#!/bin/bash
# op-require-base.sh <path> [expected-base]
#
# Refuse a worktree that does not hang off the canonical base checkout.
#
# Lake's shared store is keyed by git-common-dir, so the partition unit is the *clone*, not the
# worktree. Every extra `git clone` therefore carries its own cache that is never shared with the
# base, and a full report run on one costs the volume a fresh copy. Dispatching a seat to a
# worktree of a second clone spends that cost silently: the lane builds, the gates pass, and the
# only symptom is the volume filling up somewhere no one is looking.
#
# Occupancy is judged by `df` and by before/after deltas around a deletion. `du` cannot be used:
# it counts clonefile and hard-linked blocks once per path, so summing the top-level directories
# on this host reported 1842 GiB against a volume using 791 GiB.
set -u

P="${1:?worktree path}"
EXPECTED="${2:-$HOME/Desktop/omega/trureturing/.git}"

[ -d "$P" ] || { echo "BASE_CHECK_NO_PATH $P" >&2; exit 9; }

COMMON=$(git -C "$P" rev-parse --git-common-dir 2>/dev/null) || {
  echo "BASE_CHECK_NOT_A_REPO $P" >&2; exit 9; }

# rev-parse prints a relative path when the worktree is the base checkout itself.
case "$COMMON" in
  /*) ;;
  *)  COMMON="$(cd "$P" && cd "$(dirname "$COMMON")" && pwd)/$(basename "$COMMON")" ;;
esac

if [ "$COMMON" != "$EXPECTED" ]; then
  echo "BASE_CHECK_FOREIGN_CLONE path=$P common-dir=$COMMON expected=$EXPECTED" >&2
  echo "Open the lane on the base instead: cd $(dirname "$EXPECTED") && make worktree KIND=<kind> NAME=<lane>" >&2
  exit 7
fi

echo "BASE_CHECK_OK path=$P common-dir=$COMMON free-gi=$(df -g /System/Volumes/Data 2>/dev/null | tail -1 | awk '{print $4}')"
