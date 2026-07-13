#!/usr/bin/env bash
# fkst-monitor/platform_sync: keep the deployment's fkst-packages platform pin current with dev.
# Usage: platform_sync.sh [check|sync]
#   check  (default) read-only: fetch fkst-packages origin/dev and report whether the pinned
#          rev is behind (new packages/commits available). Never mutates.
#   sync   apply: stop supervise → fast-forward the platform checkout to origin/dev →
#          re-pin .fkst/fkst.workspace.toml external_sources.rev → regenerate fkst.lock →
#          restart supervise → report. Prints the pin bump to commit.
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
REPO_ROOT="$(cd -- "$SCRIPT_DIR/../../../.." && pwd -P)"
RUN_SH="$REPO_ROOT/.fkst/scripts/run.sh"
WORKSPACE="$REPO_ROOT/.fkst/fkst.workspace.toml"
FKST_HOME="${FKST_HOME:-$HOME/.fkst/trureturing}"
ENV_FILE="$FKST_HOME/host.env"

env_val() { [[ -f "$ENV_FILE" ]] && sed -n "s/^$1=//p" "$ENV_FILE" | tail -1; }
PLATFORM_ROOT="${FKST_PLATFORM_ROOT:-$(env_val FKST_PLATFORM_ROOT)}"
BIN="${BIN:-$(env_val BIN)}"
CHECKOUT="$(env_val FKST_HOST_ROOT)"

[[ -d "$PLATFORM_ROOT/.git" ]] || { echo "platform_sync: FKST_PLATFORM_ROOT is not a git checkout: ${PLATFORM_ROOT:-<unset>}" >&2; exit 2; }
pinned_rev() { grep -oE '[0-9a-f]{40}' "$WORKSPACE" | head -1; }

fetch_dev() { git -C "$PLATFORM_ROOT" fetch -q origin dev; }
dev_head() { git -C "$PLATFORM_ROOT" rev-parse origin/dev; }

check() {
  fetch_dev
  local pin dev behind
  pin="$(pinned_rev)"; dev="$(dev_head)"
  echo "platform_sync @ $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "  platform  : $PLATFORM_ROOT"
  echo "  pinned    : ${pin:0:12}"
  echo "  origin/dev: ${dev:0:12}"
  if [[ "$pin" == "$dev" ]]; then
    echo "  status    : CURRENT (pin == origin/dev)"
    return 0
  fi
  behind="$(git -C "$PLATFORM_ROOT" rev-list --count "$pin".."$dev" 2>/dev/null || echo '?')"
  echo "  status    : BEHIND by $behind commit(s) — run 'platform_sync.sh sync' to update"
  echo "  new commits:"
  git -C "$PLATFORM_ROOT" log --oneline "$pin".."$dev" 2>/dev/null | sed 's/^/    /' | head -20
  return 1
}

sync() {
  fetch_dev
  local pin dev
  pin="$(pinned_rev)"; dev="$(dev_head)"
  if [[ "$pin" == "$dev" ]]; then echo "platform_sync: already CURRENT (${dev:0:12}); nothing to do"; return 0; fi
  echo "platform_sync: ${pin:0:12} -> ${dev:0:12}"
  [[ -x "$BIN" ]] || { echo "platform_sync: BIN not executable: ${BIN:-<unset>}" >&2; exit 2; }

  echo "  stopping supervise..."; bash "$RUN_SH" stop >/dev/null 2>&1 || true
  echo "  fast-forwarding platform to origin/dev..."
  git -C "$PLATFORM_ROOT" merge --ff-only origin/dev >/dev/null 2>&1 \
    || { echo "platform_sync: platform checkout is not fast-forwardable to origin/dev (local commits?); resolve manually" >&2; exit 2; }
  echo "  re-pinning workspace + regenerating lock..."
  PIN="$pin" DEV="$dev" python3 - "$WORKSPACE" <<'PY'
import os, sys
p = sys.argv[1]
s = open(p).read().replace(os.environ["PIN"], os.environ["DEV"])
open(p, "w").write(s)
PY
  ( cd "$REPO_ROOT" && "$BIN" host lock --project-root .fkst >/dev/null ) \
    || { echo "platform_sync: host lock failed" >&2; exit 2; }
  echo "  restarting supervise..."; BIN="$BIN" bash "$RUN_SH" supervise >/dev/null 2>&1
  sleep 8
  if bash "$RUN_SH" status 2>&1 | grep -q running; then
    echo "  OK: supervise running on platform ${dev:0:12}"
  else
    echo "  WARN: supervise not running after restart — check newest log under $FKST_HOME/logs" >&2
  fi
  # keep the engine's dedicated checkout in sync with the repo (best-effort)
  if [[ -n "$CHECKOUT" && -d "$CHECKOUT/.git" ]]; then
    git -C "$CHECKOUT" fetch -q "$REPO_ROOT" HEAD 2>/dev/null && git -C "$CHECKOUT" merge -q --ff-only FETCH_HEAD 2>/dev/null || true
  fi
  echo "  REMEMBER: commit the pin bump — .fkst/fkst.workspace.toml + .fkst/fkst.lock (rev ${dev:0:12})"
}

case "${1:-check}" in
  check) check ;;
  sync)  sync ;;
  *) echo "usage: platform_sync.sh [check|sync]" >&2; exit 2 ;;
esac
