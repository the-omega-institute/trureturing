#!/usr/bin/env bash
set -u -o pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
if [[ -f "$ROOT/tools/scripts/maintenance_log.py" ]]; then
  if [[ -n "${TRURETURING_MAINTENANCE_RUN_ID:-}" ]]; then
    export TRURETURING_MAINTENANCE_PARENT_RUN_ID="$TRURETURING_MAINTENANCE_RUN_ID"
  fi
  unset TRURETURING_MAINTENANCE_RUN_ID
  run_id=""
  if run_id="$(python3 -B "$ROOT/tools/scripts/maintenance_log.py" begin \
      --repository "$ROOT" --script warm-donor --owner-pid "$$" --parent-pid "$PPID" \
      </dev/null 2>/dev/null)" && [[ "$run_id" =~ ^[0-9a-f]{32}$ ]]; then
    export TRURETURING_MAINTENANCE_RUN_ID="$run_id"
    export TRURETURING_MAINTENANCE_SCRIPT=warm-donor
    export TRURETURING_MAINTENANCE_REPOSITORY="$ROOT"
  fi
fi
cd "$ROOT"

finish_maintenance_log() {
  local rc="$?"
  if [[ -n "${TRURETURING_MAINTENANCE_RUN_ID:-}" ]]; then
    python3 -B "$ROOT/tools/scripts/maintenance_log.py" finish \
      --repository "$ROOT" --script warm-donor \
      --run-id "$TRURETURING_MAINTENANCE_RUN_ID" --owner-pid "$$" \
      --exit-code "$rc" </dev/null >/dev/null 2>/dev/null || true
  fi
  return "$rc"
}
trap finish_maintenance_log EXIT

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
