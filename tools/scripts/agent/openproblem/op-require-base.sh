#!/bin/bash
# op-require-base.sh <path> [expected-git-common-dir]
#
# Refuse a worktree that does not hang off the canonical base checkout.
#
# Automatic cache seeding looks for a donor only inside the same clone: a linked worktree clones
# the .lake of its clone's main checkout. Unless STRATALINT_LEAN_CACHE_DONOR_REPOSITORY names an
# explicit donor, an extra `git clone` therefore provisions a separate .lake (Release restore or
# rebuild) that shares no blocks with the base, and a full report run on one costs the volume a
# fresh copy. Dispatching a seat to a worktree of a second clone spends that cost silently: the
# lane builds, the gates pass, and the only symptom is the volume filling up somewhere no one is
# looking.
#
# Occupancy is judged by `df` and by before/after deltas around a deletion. `du` cannot be used:
# it counts clonefile and hard-linked blocks once per path, so summing the top-level directories
# on this host reported 1842 GiB against a volume using 791 GiB.
#
# Without an explicit argument the base is the clone that holds this script.
set -u

P="${1:?worktree path}"

common_dir() {
  local dir
  dir=$(git -C "$1" rev-parse --path-format=absolute --git-common-dir 2>/dev/null) || return 1
  (CDPATH= cd -- "$dir" && pwd -P)
}

if [ -n "${2:-}" ]; then
  EXPECTED=$(CDPATH= cd -- "$2" 2>/dev/null && pwd -P) || { echo "BASE_CHECK_NO_EXPECTED $2" >&2; exit 9; }
else
  EXPECTED=$(common_dir "$(dirname "$0")") || {
    echo "BASE_CHECK_NO_DEFAULT script is not inside a git checkout: $0" >&2; exit 9; }
fi

[ -d "$P" ] || { echo "BASE_CHECK_NO_PATH $P" >&2; exit 9; }

COMMON=$(common_dir "$P") || { echo "BASE_CHECK_NOT_A_REPO $P" >&2; exit 9; }

if [ "$COMMON" != "$EXPECTED" ]; then
  echo "BASE_CHECK_FOREIGN_CLONE path=$P common-dir=$COMMON expected=$EXPECTED" >&2
  echo "Open the lane on the base instead: cd $(dirname "$EXPECTED") && make worktree KIND=<kind> NAME=<lane>" >&2
  exit 7
fi

echo "BASE_CHECK_OK path=$P common-dir=$COMMON free-gi=$(df -g /System/Volumes/Data 2>/dev/null | tail -1 | awk '{print $4}')"
