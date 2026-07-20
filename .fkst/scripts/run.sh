#!/usr/bin/env bash
set -euo pipefail

readonly FKST_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
readonly REPO_ROOT="$(cd -- "$FKST_ROOT/.." && pwd -P)"
readonly OPERATE_ROOT="${FKST_OPERATE_ROOT:-$HOME/.fkst/trureturing}"
readonly ENV_FILE="$OPERATE_ROOT/host.env"
readonly LOG_DIR="$OPERATE_ROOT/logs"
readonly PLATFORM_PACKAGES="github-proxy consensus github-devloop github-devloop-pr github-devloop-integration github-devloop-intake github-devloop-intake-default github-devloop-workflow github-devloop-decompose github-devloop-ops github-external-pr-intake idle-detector"

die() {
  printf 'fkst: %s\n' "$*" >&2
  exit 1
}

shell_value() {
  printf '%q' "$1"
}

primary_worktree() {
  git -C "$REPO_ROOT" worktree list --porcelain 2>/dev/null \
    | awk '/^worktree / { sub(/^worktree /, ""); print; exit }'
}

discover_platform_root() {
  local primary candidate
  primary="$(primary_worktree)"
  [[ -n "$primary" ]] || return 1
  candidate="$(dirname -- "$primary")/fkst-packages"
  [[ -x "$candidate/scripts/run.sh" ]] || return 1
  printf '%s\n' "$candidate"
}

discover_bin() {
  local primary candidate
  if command -v fkst-framework >/dev/null 2>&1; then
    command -v fkst-framework
    return
  fi
  primary="$(primary_worktree)"
  [[ -n "$primary" ]] || return 1
  candidate="$(dirname -- "$primary")/fkst-substrate/target/debug/fkst-framework"
  [[ -x "$candidate" ]] || return 1
  printf '%s\n' "$candidate"
}

ensure_host_env() {
  local bin platform
  mkdir -p "$OPERATE_ROOT/durable" "$OPERATE_ROOT/runtime" "$LOG_DIR" "$HOME/.fkst/rate-pools"
  [[ ! -e "$ENV_FILE" ]] || return 0
  bin="$(discover_bin)" || die "cannot discover BIN; put fkst-framework on PATH"
  platform="$(discover_platform_root)" \
    || die "cannot discover sibling fkst-packages checkout"
  {
    printf '# Generated host-local configuration. Do not commit.\n'
    printf 'BIN=%s\n' "$(shell_value "$bin")"
    printf 'FKST_HOST_ROOT=%s\n' "$(shell_value "$OPERATE_ROOT/checkout")"
    printf 'FKST_PLATFORM_ROOT=%s\n' "$(shell_value "$platform")"
    printf 'FKST_DURABLE_ROOT=%s\n' "$(shell_value "$OPERATE_ROOT/durable")"
    printf 'FKST_RUNTIME_ROOT=%s\n' "$(shell_value "$OPERATE_ROOT/runtime")"
    printf 'FKST_RATE_POOL_ROOT=%s\n' "$(shell_value "$HOME/.fkst/rate-pools")"
    printf 'FKST_GITHUB_REPO=the-omega-institute/trureturing\n'
    printf 'unset FKST_GITHUB_WRITE\n'
    printf 'FKST_GITHUB_BOT_LOGIN=ElonSG\n'
    printf 'FKST_GITHUB_PROXY_POLL_LABEL_PREFIX=fkst-dev:\n'
    printf 'FKST_DEVLOOP_UPSTREAM_BRANCH=dev\n'
    printf 'FKST_DEVLOOP_INTEGRATION_BRANCH=integration-ElonSG\n'
    printf 'FKST_DEVLOOP_ROLLUP_MERGE=auto\n'
  } >"$ENV_FILE"
  chmod 600 "$ENV_FILE"
}

load_host_env() {
  ensure_host_env
  set -a
  # shellcheck disable=SC1090
  source "$ENV_FILE"
  set +a
  # GitHub write posture is a host-local operational fact carried by host.env
  # (gitignored, not committed): unset/anything-but-1 = dry-run; 1 = real writes.
  # A freshly generated host.env defaults to dry-run (see ensure_host_env); the
  # operator opts into real writes by editing their own host.env.
  [[ -x "${BIN:-}" ]] || die "host.env BIN is not executable: ${BIN:-<unset>}"
  [[ -x "${FKST_PLATFORM_ROOT:-}/scripts/run.sh" ]] \
    || die "host.env FKST_PLATFORM_ROOT is invalid: ${FKST_PLATFORM_ROOT:-<unset>}"
  [[ "${FKST_GITHUB_REPO:-}" == "the-omega-institute/trureturing" ]] \
    || die "host.env targets unexpected repository: ${FKST_GITHUB_REPO:-<unset>}"
}

pid_file() {
  printf '%s/.fkst-supervise.pid\n' "$OPERATE_ROOT/durable"
}

read_live_pid() {
  local file pid
  file="$(pid_file)"
  [[ -f "$file" ]] || return 1
  pid="$(sed -n '1p' "$file")"
  [[ "$pid" =~ ^[0-9]+$ ]] || return 1
  kill -0 "$pid" 2>/dev/null || return 1
  printf '%s\n' "$pid"
}

start() {
  local checkout_root log pid
  load_host_env
  checkout_root="${FKST_HOST_ROOT:-$OPERATE_ROOT/checkout}"
  [[ -d "$checkout_root" ]] || die "dedicated checkout does not exist: $checkout_root"
  test -e "$checkout_root/.git" || die "dedicated checkout is not a git checkout: $checkout_root"
  checkout_root="$(cd -- "$checkout_root" && pwd -P)"
  [[ "$checkout_root" != "$REPO_ROOT" ]] \
    || die "dedicated checkout must not be the source worktree: $checkout_root"
  log="$LOG_DIR/supervise-$(date -u +%Y%m%dT%H%M%SZ).log"
  ln -sfn "$(basename -- "$log")" "$LOG_DIR/latest.log"
  (
    cd -- "$checkout_root"
    exec nohup bash "$FKST_PLATFORM_ROOT/scripts/run.sh" supervise \
      --project-root "$checkout_root" \
      --platform-root "$FKST_PLATFORM_ROOT" \
      --platform-packages "$PLATFORM_PACKAGES" \
      --durable-root "$FKST_DURABLE_ROOT" \
      --runtime-root "$FKST_RUNTIME_ROOT" \
      --restart
  ) >>"$log" 2>&1 &
  pid=$!
  sleep 2
  if ! kill -0 "$pid" 2>/dev/null; then
    wait "$pid" || true
    die "supervise exited during startup; see $log"
  fi
  printf 'fkst: started pid %s; log %s\n' "$pid" "$log"
}

stop() {
  local pid attempts=0 file
  ensure_host_env
  file="$(pid_file)"
  if ! pid="$(read_live_pid)"; then
    rm -f "$file"
    printf 'fkst: stopped\n'
    return
  fi
  kill "$pid" 2>/dev/null || true
  while kill -0 "$pid" 2>/dev/null && [[ "$attempts" -lt 50 ]]; do
    sleep 0.1
    attempts=$((attempts + 1))
  done
  if kill -0 "$pid" 2>/dev/null; then
    kill -9 "$pid" 2>/dev/null || true
    printf 'fkst: forced stop pid %s\n' "$pid"
  else
    printf 'fkst: stopped pid %s\n' "$pid"
  fi
  rm -f "$file"
}

status() {
  local pid
  ensure_host_env
  if pid="$(read_live_pid)"; then
    printf 'fkst: running pid %s\n' "$pid"
    return 0
  fi
  printf 'fkst: stopped\n'
  return 1
}

logs() {
  ensure_host_env
  [[ -e "$LOG_DIR/latest.log" ]] || die "no supervise log exists"
  tail -n "${LINES:-120}" "$LOG_DIR/latest.log"
}

[[ $# -eq 1 ]] || die "usage: $0 supervise|stop|status|logs"
case "$1" in
  supervise) start ;;
  stop) stop ;;
  status) status ;;
  logs) logs ;;
  *) die "usage: $0 supervise|stop|status|logs" ;;
esac
