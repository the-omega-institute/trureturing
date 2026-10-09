#!/usr/bin/env bash
set -u -o pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
cd "$ROOT"

receipt() {
  local status="$1"
  local phase="$2"
  local reason="${3:-}"
  if [[ -n "$reason" ]]; then
    printf 'LEAN_DONOR_WARM {"status":"%s","phase":"%s","reason":"%s"}\n' \
      "$status" "$phase" "$reason"
  else
    printf 'LEAN_DONOR_WARM {"status":"%s","phase":"%s","reason":null}\n' \
      "$status" "$phase"
  fi
}

branch="$(git symbolic-ref --quiet --short HEAD 2>/dev/null)"
if [[ "$branch" != "dev" ]]; then
  receipt skipped precondition "branch is not dev"
  exit 0
fi

tree_status="$(git status --porcelain --untracked-files=normal)"
status_rc=$?
if (( status_rc != 0 )); then
  receipt failed precondition "git status failed"
  exit "$status_rc"
fi
if [[ -n "$tree_status" ]]; then
  receipt skipped precondition "worktree is not clean"
  exit 0
fi

git pull --ff-only origin dev
pull_rc=$?
if (( pull_rc != 0 )); then
  receipt failed pull "git pull --ff-only origin dev failed"
  exit "$pull_rc"
fi

make -C "$ROOT" lean
lean_rc=$?
if (( lean_rc != 0 )); then
  receipt failed lean "make lean failed"
  exit "$lean_rc"
fi

# A rebuilt donor no longer shares blocks with existing worktrees; re-share what is identical.
make -C "$ROOT" lean-cache-dedupe ALL=1 \
  || printf 'warm-donor: worktree re-share failed; the donor itself is warm\n' >&2

receipt warmed complete
