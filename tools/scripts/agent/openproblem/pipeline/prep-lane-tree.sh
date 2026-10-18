#!/bin/bash
# Merge origin/dev without rebasing, preserve dirty lanes, and ensure the Lean cache.
set -uo pipefail
. "$(dirname "$0")/common.sh"
[ "${1:-}" != --selftest ] || { op_selftest prep-lane-tree; exit $?; }
[ "$#" -eq 1 ] || op_fail 10 USAGE 'prep-lane-tree.sh WORKTREE'
op_init; op_need make
[ -d "$1" ] || op_fail 11 INPUT_MISSING "$1"
cd "$1" || op_fail 11 INPUT_MISSING "$1"
git rev-parse --show-toplevel >/dev/null || op_fail 11 NOT_WORKTREE "$1"
git fetch -q origin dev || { echo 'PREP=3 fetch'; exit 3; }
ahead=$(git rev-list --count origin/dev..HEAD) || op_fail 16 GIT_FAILED rev-list
dirty=$(git status --porcelain --untracked-files=no) || op_fail 16 GIT_FAILED status
if git merge-base --is-ancestor origin/dev HEAD; then
  echo 'already contains origin/dev'
elif [ "$ahead" = 0 ]; then
  git merge --ff-only -q origin/dev || { echo "PREP=4 ff-blocked $1"; exit 4; }
elif [ -z "$dirty" ]; then
  git merge --no-edit -q origin/dev || { git merge --abort; echo "PREP=5 conflict $1"; exit 5; }
else echo "PREP=6 dirty-with-commits $1"; exit 6; fi
make lean-cache-ensure; rc=$?
echo "PREP=$rc $1"
exit "$rc"
