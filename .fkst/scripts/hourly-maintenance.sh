#!/usr/bin/env bash
# Canonical hourly engine maintenance: platform pin/lock sync, checkout FF, restart policy,
# worktree collection, and stuck Lean build/slot collection.
set -uo pipefail

CHANGED=0
PLATFORM_CHANGED=0
CHECKOUT_DEV_REV=""
PLATFORM_CURRENT_REV=""
PLATFORM_DEV_REV=""
PLATFORM_WORKSPACE_BACKUP=""
PLATFORM_LOCK_BACKUP=""

say() {
  printf '[%s] %s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$*" \
    | tee -a "$FKST_MAINTENANCE_LOG"
}

require_parameter() {
  local name="$1"
  [[ -n "${!name:-}" ]] || {
    printf 'hourly-maintenance: required parameter %s is unset\n' "$name" >&2
    return 2
  }
}

require_absolute_path() {
  local name="$1"
  [[ "${!name}" == /* ]] || {
    printf 'hourly-maintenance: %s must be an absolute path\n' "$name" >&2
    return 2
  }
}

validate_configuration() {
  local name
  for name in \
    FKST_CHECKOUT_ROOT \
    FKST_PLATFORM_ROOT \
    FKST_FRAMEWORK_BIN \
    FKST_RUN_SCRIPT \
    FKST_MAINTENANCE_LOG \
    FKST_WORKTREE_ROOT \
    FKST_REPORT_SLOT_ROOT \
    FKST_TIMEOUT_BIN \
    FKST_GITHUB_REPOSITORY \
    FKST_LAUNCHD_LABEL; do
    require_parameter "$name" || return
  done
  for name in \
    FKST_CHECKOUT_ROOT \
    FKST_PLATFORM_ROOT \
    FKST_FRAMEWORK_BIN \
    FKST_RUN_SCRIPT \
    FKST_MAINTENANCE_LOG \
    FKST_WORKTREE_ROOT \
    FKST_REPORT_SLOT_ROOT \
    FKST_TIMEOUT_BIN; do
    require_absolute_path "$name" || return
  done
  [[ -d "$(dirname -- "$FKST_MAINTENANCE_LOG")" ]] || {
    printf 'hourly-maintenance: log directory does not exist: %s\n' \
      "$(dirname -- "$FKST_MAINTENANCE_LOG")" >&2
    return 2
  }
}

restore_platform_bytes() {
  [[ -n "$PLATFORM_WORKSPACE_BACKUP" && -f "$PLATFORM_WORKSPACE_BACKUP" ]] \
    || { say "ROLLBACK-FAIL: workspace backup unavailable"; return 1; }
  [[ -n "$PLATFORM_LOCK_BACKUP" && -f "$PLATFORM_LOCK_BACKUP" ]] \
    || { say "ROLLBACK-FAIL: lock backup unavailable"; return 1; }

  cp "$PLATFORM_WORKSPACE_BACKUP" "$FKST_CHECKOUT_ROOT/fkst.workspace.toml" \
    && cp "$PLATFORM_LOCK_BACKUP" "$FKST_CHECKOUT_ROOT/fkst.lock"
}

rollback_platform() {
  restore_platform_bytes || return 1
  if ! "$FKST_TIMEOUT_BIN" 240 "$FKST_FRAMEWORK_BIN" host lock \
      --project-root "$FKST_CHECKOUT_ROOT" >/dev/null 2>&1; then
    say "ROLLBACK-HOST-LOCK-FAIL; preserving original pin and lock bytes"
  fi
  # host lock may rewrite the lock even for the restored pin. The rollback contract is the
  # exact pre-cycle bytes, so restore once more after the validation attempt.
  restore_platform_bytes
}

sync_platform() {
  git -C "$FKST_PLATFORM_ROOT" fetch origin dev >/dev/null 2>&1 \
    || { say "PLAT-FETCH-FAIL"; return 1; }

  # Issue #2461: the deployed engine reads checkout/fkst.workspace.toml, not the committed
  # checkout/.fkst copy. The deployed top-level file is therefore the only pin updated here.
  PLATFORM_CURRENT_REV="$(
    grep -oE '[0-9a-f]{40}' "$FKST_CHECKOUT_ROOT/fkst.workspace.toml" 2>/dev/null \
      | head -1
  )"
  PLATFORM_DEV_REV="$(git -C "$FKST_PLATFORM_ROOT" rev-parse origin/dev 2>/dev/null)"
  [[ "$PLATFORM_CURRENT_REV" =~ ^[0-9a-f]{40}$ ]] \
    || { say "invalid deployed platform pin"; return 1; }
  [[ "$PLATFORM_DEV_REV" =~ ^[0-9a-f]{40}$ ]] \
    || { say "no platform origin/dev"; return 1; }

  if [[ "$PLATFORM_CURRENT_REV" == "$PLATFORM_DEV_REV" ]]; then
    say "PLATFORM CURRENT (${PLATFORM_CURRENT_REV:0:12})"
    return 0
  fi

  local stamp temporary_workspace
  stamp="$(date -u +%Y%m%d-%H%M%S)"
  PLATFORM_WORKSPACE_BACKUP="$FKST_CHECKOUT_ROOT/fkst.workspace.toml.bak-$stamp"
  PLATFORM_LOCK_BACKUP="$FKST_CHECKOUT_ROOT/fkst.lock.bak-$stamp"
  temporary_workspace="$FKST_CHECKOUT_ROOT/fkst.workspace.toml.next-$stamp"
  cp "$FKST_CHECKOUT_ROOT/fkst.workspace.toml" "$PLATFORM_WORKSPACE_BACKUP" \
    && cp "$FKST_CHECKOUT_ROOT/fkst.lock" "$PLATFORM_LOCK_BACKUP" \
    || { say "PLATFORM-BACKUP-FAIL"; return 1; }

  say "PLATFORM BEHIND ${PLATFORM_CURRENT_REV:0:12} -> ${PLATFORM_DEV_REV:0:12}; syncing"
  if ! sed "s/$PLATFORM_CURRENT_REV/$PLATFORM_DEV_REV/g" \
      "$FKST_CHECKOUT_ROOT/fkst.workspace.toml" > "$temporary_workspace" \
      || ! mv "$temporary_workspace" "$FKST_CHECKOUT_ROOT/fkst.workspace.toml"; then
    rm -f "$temporary_workspace"
    if rollback_platform; then
      say "PLATFORM-PIN-WRITE-FAIL; reverted platform"
    else
      say "PLATFORM-PIN-WRITE-FAIL; rollback failed, original bytes not confirmed"
    fi
    return 1
  fi

  if ! "$FKST_TIMEOUT_BIN" 240 "$FKST_FRAMEWORK_BIN" host lock \
      --project-root "$FKST_CHECKOUT_ROOT" >/dev/null 2>&1; then
    say "HOST-LOCK-FAIL for ${PLATFORM_DEV_REV:0:12}; reverting platform"
    rollback_platform
    return 1
  fi

  PLATFORM_CHANGED=1
  CHANGED=1
}

sync_checkout() {
  if ! git -C "$FKST_CHECKOUT_ROOT" fetch origin dev >/dev/null 2>&1; then
    say "CHECKOUT-FETCH-FAIL; skipped checkout sync"
    return 0
  fi

  local checkout_head checkout_status behind
  checkout_head="$(git -C "$FKST_CHECKOUT_ROOT" rev-parse HEAD 2>/dev/null)"
  CHECKOUT_DEV_REV="$(git -C "$FKST_CHECKOUT_ROOT" rev-parse origin/dev 2>/dev/null)"
  if [[ -z "$checkout_head" || -z "$CHECKOUT_DEV_REV" ]]; then
    say "CHECKOUT-REV-PARSE-FAIL; skipped checkout sync"
    return 0
  fi
  if [[ "$checkout_head" == "$CHECKOUT_DEV_REV" ]]; then
    say "CHECKOUT CURRENT (${checkout_head:0:12})"
    return 0
  fi
  if ! git -C "$FKST_CHECKOUT_ROOT" merge-base --is-ancestor \
      "$checkout_head" "$CHECKOUT_DEV_REV" >/dev/null 2>&1; then
    say "CHECKOUT DIVERGED from origin/dev; not auto-FF (manual review)"
    return 0
  fi

  # Only TRACKED modifications may block the fast-forward. Untracked files provably do not
  # prevent one -- `git merge --ff-only` succeeds with them present -- and `--ff-only` below is
  # already the correct arbiter for the one case that matters, an untracked file the merge would
  # overwrite, which it refuses on its own.
  #
  # Counting untracked files as "uncommitted changes" froze the deployed checkout permanently on
  # a real host: this tool's own rollback backups (fkst.lock.bak-*, fkst.workspace.toml.bak-*) are
  # created every run, so the guard blocked the very fast-forward the backups exist to protect;
  # and `.metadata_never_index`, an intentional Spotlight-exclusion marker that must stay, blocked
  # it on its own even after every backup was cleaned. The checkout sat 24 commits behind with no
  # path forward.
  if ! checkout_status="$(
      git -C "$FKST_CHECKOUT_ROOT" status --porcelain --untracked-files=no 2>/dev/null
    )"; then
    say "CHECKOUT-STATUS-FAIL; skipped checkout sync"
    return 0
  fi
  if [[ -n "$checkout_status" ]]; then
    say "CHECKOUT-FF-BLOCKED (uncommitted changes); skipped, engine stays on ${checkout_head:0:12}"
    return 0
  fi

  behind="$(git -C "$FKST_CHECKOUT_ROOT" rev-list \
    "$checkout_head..$CHECKOUT_DEV_REV" --count 2>/dev/null)"
  say "CHECKOUT BEHIND ${checkout_head:0:12} -> ${CHECKOUT_DEV_REV:0:12} ($behind commits); FF"
  if git -C "$FKST_CHECKOUT_ROOT" merge --ff-only "$CHECKOUT_DEV_REV" >/dev/null 2>&1; then
    CHANGED=1
  else
    say "CHECKOUT-FF-BLOCKED; skipped, engine stays on ${checkout_head:0:12}"
  fi
}

canonical_gc_root() {
  local root="$1" resolved relative
  [[ -d "$root" ]] || return 1
  resolved="$(cd -- "$root" 2>/dev/null && pwd -P)" || return 1
  relative="${resolved#/}"
  [[ "$resolved" == /* && "$resolved" != "/" && "$relative" == */* ]] || return 1
  printf '%s\n' "$resolved"
}

lane_is_clean_and_unowned() {
  local lane="$1" status own_commits
  git -C "$lane" rev-parse --is-inside-work-tree >/dev/null 2>&1 || return 1
  status="$(git -C "$lane" status --porcelain --untracked-files=normal 2>/dev/null)" \
    || return 1
  [[ -z "$status" ]] || return 1
  own_commits="$(git -C "$lane" rev-list --count origin/dev..HEAD 2>/dev/null)" \
    || return 1
  [[ "$own_commits" == "0" ]]
}

gc_worktrees() {
  local root
  [[ -d "$FKST_WORKTREE_ROOT" ]] || return 0
  root="$(canonical_gc_root "$FKST_WORKTREE_ROOT")" \
    || { say "WT-GC skipped (unsafe root)"; return 0; }

  local removed=0 directory lane issue_number state eligible
  for directory in "$root"/*/; do
    [[ -d "$directory" ]] || continue
    lane="$(basename -- "$directory")"
    if ! lane_is_clean_and_unowned "$directory"; then
      say "WT-GC retained $lane (own commits, uncommitted work, or unverifiable ancestry)"
      continue
    fi

    eligible=0
    if [[ "$lane" =~ ([0-9]+)-[0-9]+$ ]]; then
      issue_number="${BASH_REMATCH[1]}"
      state="$(gh issue view "$issue_number" \
        --repo "$FKST_GITHUB_REPOSITORY" --json state --jq '.state' 2>/dev/null)"
      [[ "$state" == "CLOSED" ]] && eligible=1
    fi
    [[ "$eligible" == "1" ]] || continue

    if git -C "$FKST_CHECKOUT_ROOT" worktree remove "${directory%/}" >/dev/null 2>&1; then
      removed=$((removed + 1))
    else
      say "WT-GC retained $lane (git refused removal)"
    fi
  done
  if [[ "$removed" -gt 0 ]]; then
    git -C "$FKST_CHECKOUT_ROOT" worktree prune >/dev/null 2>&1 || true
    say "WT-GC removed $removed orphan worktree(s)"
  fi
}

reclaim_stale_slots() {
  local root
  [[ -d "$FKST_REPORT_SLOT_ROOT" ]] || return 0
  root="$(canonical_gc_root "$FKST_REPORT_SLOT_ROOT")" \
    || { say "STUCK-LEAN-GC skipped slot reclaim (unsafe root)"; return 0; }

  local lock owner confirmed_owner live_pid guard reclaimed
  for lock in "$root"/*.lock; do
    [[ -e "$lock/owner" ]] || continue
    owner="$(grep -oE '^[0-9]+' "$lock/owner" 2>/dev/null | head -1)"
    [[ -n "$owner" ]] || continue
    kill -0 "$owner" 2>/dev/null && continue
    live_pid="$(ps -p "$owner" -o pid= 2>/dev/null | tr -d '[:space:]')"
    [[ -z "$live_pid" ]] || continue

    guard="$lock.reclaim-guard"
    mkdir "$guard" 2>/dev/null || continue
    confirmed_owner="$(grep -oE '^[0-9]+' "$lock/owner" 2>/dev/null | head -1)"
    if [[ "$confirmed_owner" != "$owner" ]] \
        || kill -0 "$owner" 2>/dev/null \
        || [[ -n "$(ps -p "$owner" -o pid= 2>/dev/null | tr -d '[:space:]')" ]]; then
      rmdir "$guard" 2>/dev/null || true
      continue
    fi

    reclaimed="$lock.reclaimed-$$-$RANDOM"
    if mv "$lock" "$reclaimed" 2>/dev/null; then
      rm -rf -- "$reclaimed"
    fi
    rmdir "$guard" 2>/dev/null || true
  done
}

gc_stuck_lean_builds() {
  reclaim_stale_slots
}

cleanup_old_backups() {
  find "$FKST_CHECKOUT_ROOT" -maxdepth 1 -name '*.bak-*' -mtime +3 -delete \
    2>/dev/null || true
}

engine_pid() {
  local escaped_root
  escaped_root="$(printf '%s' "$FKST_CHECKOUT_ROOT" | sed 's/[][\\.^$*+?{}|()]/\\&/g')"
  pgrep -f "fkst-framework.*supervise --project-root $escaped_root" 2>/dev/null | head -1
}

restart_engine() {
  local previous_pid
  previous_pid="$(engine_pid)"
  if ! bash "$FKST_RUN_SCRIPT" stop >/dev/null 2>&1; then
    say "RESTART-STOP-FAIL; engine state unchanged"
    return 1
  fi
  sleep 10
  sleep 20

  local launch_count pid
  launch_count="$(launchctl list 2>/dev/null | grep -cF "$FKST_LAUNCHD_LABEL" || true)"
  pid="$(engine_pid)"
  if [[ "$launch_count" == "0" || -z "$pid" \
      || ( -n "$previous_pid" && "$pid" == "$previous_pid" ) ]]; then
    say "UNHEALTHY after restart (launchd=$launch_count old_pid=${previous_pid:-none} new_pid=${pid:-none})"
    if [[ "$PLATFORM_CHANGED" == "1" ]]; then
      if rollback_platform; then
        bash "$FKST_RUN_SCRIPT" stop >/dev/null 2>&1
        sleep 8
        say "reverted platform to ${PLATFORM_CURRENT_REV:0:12}"
      else
        say "PLATFORM-ROLLBACK-FAIL after unhealthy restart; original bytes not confirmed"
      fi
    fi
    return 1
  fi

  say "SYNCED OK (engine pid $pid; platform ${PLATFORM_DEV_REV:0:12}; checkout $([ -n "$CHECKOUT_DEV_REV" ] && printf '%s' "${CHECKOUT_DEV_REV:0:12}" || printf 'n/a'))"
  cleanup_old_backups
}

restart_if_needed() {
  if [[ "$CHANGED" == "0" ]]; then
    say "ALL CURRENT; no restart"
    return 0
  fi

  local alive implementing
  alive="$(engine_pid)"
  if [[ -n "$alive" ]]; then
    if ! command -v gh >/dev/null 2>&1; then
      say "DEFER-RESTART: implementing issue state unavailable; engine alive (pid $alive)"
      cleanup_old_backups
      return 0
    fi
    if ! implementing="$(
        LEAN4_GUARDRAILS_BYPASS=1 gh issue list \
        --repo "$FKST_GITHUB_REPOSITORY" \
        --state open \
        --label 'fkst-dev:implementing' \
        --json number \
        --jq 'length' 2>/dev/null
      )"; then
      say "DEFER-RESTART: implementing issue state unavailable; engine alive (pid $alive)"
      cleanup_old_backups
      return 0
    fi
    if [[ ! "$implementing" =~ ^[0-9]+$ ]]; then
      say "DEFER-RESTART: implementing issue state unavailable; engine alive (pid $alive)"
      cleanup_old_backups
      return 0
    fi
    if [[ "$implementing" -gt 0 ]]; then
      say "DEFER-RESTART: $implementing issue(s) implementing + engine alive (pid $alive); pin updated, restart deferred"
      cleanup_old_backups
      return 0
    fi
  fi

  restart_engine
}

main() {
  validate_configuration || return
  sync_platform || return
  sync_checkout
  gc_worktrees
  gc_stuck_lean_builds
  restart_if_needed
}

if [[ "${BASH_SOURCE[0]}" == "$0" ]]; then
  main "$@"
fi
