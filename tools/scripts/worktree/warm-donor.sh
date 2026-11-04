#!/usr/bin/env bash
set -u -o pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
if [[ "${TRURETURING_MAINTENANCE_LOG_WARM_DONOR:-0}" != 1 && -f "$ROOT/tools/scripts/maintenance_log.py" ]]; then
  export TRURETURING_MAINTENANCE_LOG_WARM_DONOR=1
  exec python3 -B "$ROOT/tools/scripts/maintenance_log.py" run \
    --repository "$ROOT" --script warm-donor -- \
    /bin/bash "$ROOT/tools/scripts/worktree/warm-donor.sh" "$@"
fi
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

if [[ -f "$ROOT/.lake/build/stratalint/raw-lean-report.json" ]]; then
  python3 -B "$ROOT/tools/lean-inspector/reuse.py" refresh-stale-seed --repository "$ROOT"
  refresh_rc=$?
  if (( refresh_rc != 0 )); then
    receipt failed refresh "stale seed refresh failed"
    exit "$refresh_rc"
  fi
fi

make -C "$ROOT" lean
lean_rc=$?
if (( lean_rc != 0 )); then
  receipt failed lean "make lean failed"
  exit "$lean_rc"
fi

receipt warmed complete
