#!/usr/bin/env bash
# pr-watch runtime identity cases sourced by hourly-maintenance-behavior.sh.

pr_watch_process_start_for_test() {
  LC_ALL=C command ps -p "$1" -o lstart= 2>/dev/null \
    | command sed 's/^[[:space:]]*//;s/[[:space:]]*$//'
}

start_pr_watch_fixture() {
  local root="$1" physical_root physical_checkout loaded_blob process_start
  physical_root="$(cd "$root" && pwd -P)"
  physical_checkout="$(cd "$CHECKOUT_ROOT" && pwd -P)"
  PR_WATCH_STATE="$physical_root/pr-watch.state"
  PR_WATCH_LOADED_SCRIPT="$physical_root/pr-watch-loaded.sh"
  PR_WATCH_CANONICAL_SCRIPT="$physical_checkout/Meta/StrataLint/scripts/pr-shepherd.sh"
  command cp "$PR_WATCH_CANONICAL_SCRIPT" "$PR_WATCH_LOADED_SCRIPT"
  /bin/bash "$PR_WATCH_LOADED_SCRIPT" watch 60 300 &
  PR_WATCH_PID=$!
  export PR_WATCH_PID
  loaded_blob="$(command git -C "$CHECKOUT_ROOT" hash-object "$PR_WATCH_LOADED_SCRIPT")"
  process_start="$(pr_watch_process_start_for_test "$PR_WATCH_PID")"
  [[ -n "$process_start" ]] || return 1
  cat > "$PR_WATCH_STATE" <<EOF
schema=pr-watch-state-v1
pid=$PR_WATCH_PID
process_start=$process_start
canonical_script=$PR_WATCH_CANONICAL_SCRIPT
loaded_script=$PR_WATCH_LOADED_SCRIPT
loaded_blob=$loaded_blob
interval=60
max_cycles=300
cycle=1
EOF
  export PR_SHEPHERD_PID="$PR_WATCH_STATE"
}

stop_pr_watch_fixture() {
  command kill "$PR_WATCH_PID" 2>/dev/null || true
  command wait "$PR_WATCH_PID" 2>/dev/null || true
}

configure_pr_watch_maintenance_fixture() {
  local root="$1"
  mkdir -p "$root/logs"
  LOG_FILE="$root/logs/hourly-maintenance.log"
  export FKST_MAINTENANCE_LOG="$LOG_FILE"
  create_checkout_history_fixture "$root" || return 1
  export FKST_HOST_ROOT="$CHECKOUT_ROOT"
  CHECKOUT_DEV_REV="$(command git -C "$CHECKOUT_ROOT" rev-parse HEAD)"
  start_pr_watch_fixture "$root" || return 1
}

advance_checkout_pr_watch() {
  local repository="$1" contents="$2"
  printf '%s\n' "$contents" >> "$repository/Meta/StrataLint/scripts/pr-shepherd.sh"
  command git -C "$repository" add Meta/StrataLint/scripts/pr-shepherd.sh
  git_quiet -C "$repository" commit -m "advance pr-watch" || return 1
  git_quiet -C "$repository" push origin dev || return 1
  CHECKOUT_DEV_REV="$(command git -C "$repository" rev-parse HEAD)"
}

current_pr_watch_identity_is_accepted() (
  load_implementation || exit 1
  local root
  root="$(mktemp -d -t hourly-maintenance-pr-watch-current.XXXXXX)" || exit 1
  trap 'stop_pr_watch_fixture; rm -rf "$root"' EXIT
  configure_pr_watch_maintenance_fixture "$root" || exit 1

  reconcile_pr_watch || fail "current pr-watch identity was rejected"
  command grep -q 'PR-WATCH CURRENT' "$LOG_FILE" \
    || fail "current pr-watch identity was not reported"
)

stale_pr_watch_identity_schedules_boundary_convergence() (
  load_implementation || exit 1
  local root
  root="$(mktemp -d -t hourly-maintenance-pr-watch-behind.XXXXXX)" || exit 1
  trap 'stop_pr_watch_fixture; rm -rf "$root"' EXIT
  configure_pr_watch_maintenance_fixture "$root" || exit 1
  advance_checkout_pr_watch "$CHECKOUT_ROOT" '# replacement' || exit 1

  reconcile_pr_watch || fail "reloadable stale pr-watch identity should be nonfatal"
  command grep -q 'PR-WATCH BEHIND .*boundary reload pending' "$LOG_FILE" \
    || fail "stale pr-watch identity did not schedule boundary convergence"
)

post_boundary_reload_identity_is_verified() (
  load_implementation || exit 1
  local root
  root="$(mktemp -d -t hourly-maintenance-pr-watch-reloaded.XXXXXX)" || exit 1
  trap 'stop_pr_watch_fixture; rm -rf "$root"' EXIT
  configure_pr_watch_maintenance_fixture "$root" || exit 1
  advance_checkout_pr_watch "$CHECKOUT_ROOT" '# replacement' || exit 1
  reconcile_pr_watch || fail "reloadable stale pr-watch identity should be nonfatal"

  stop_pr_watch_fixture
  start_pr_watch_fixture "$root" || exit 1
  reconcile_pr_watch || fail "post-boundary pr-watch identity was rejected"
  command grep -q 'PR-WATCH BEHIND' "$LOG_FILE" \
    || fail "pre-reload stale identity was not reported"
  command grep -q 'PR-WATCH CURRENT' "$LOG_FILE" \
    || fail "post-boundary identity was not verified"
)

checkout_drift_blocks_pr_watch_convergence() (
  load_implementation || exit 1
  local root
  root="$(mktemp -d -t hourly-maintenance-pr-watch-blocked.XXXXXX)" || exit 1
  trap 'stop_pr_watch_fixture; rm -rf "$root"' EXIT
  configure_pr_watch_maintenance_fixture "$root" || exit 1
  advance_checkout_pr_watch "$CHECKOUT_WRITER" '# remote replacement' || exit 1
  command git -C "$CHECKOUT_ROOT" fetch origin dev >/dev/null 2>&1 || exit 1

  reconcile_pr_watch && fail "checkout drift must block pr-watch convergence"
  command grep -q 'PR-WATCH RELOAD BLOCKED' "$LOG_FILE" \
    || fail "blocked pr-watch convergence was not reported"
)

unverifiable_pr_watch_identity_fails_closed() (
  load_implementation || exit 1
  local root
  root="$(mktemp -d -t hourly-maintenance-pr-watch-unknown.XXXXXX)" || exit 1
  trap 'stop_pr_watch_fixture; rm -rf "$root"' EXIT
  configure_pr_watch_maintenance_fixture "$root" || exit 1
  command sed -i.bak 's/^loaded_blob=.*/loaded_blob=0000000000000000000000000000000000000000/' \
    "$PR_WATCH_STATE"

  reconcile_pr_watch && fail "unverifiable pr-watch identity was accepted"
  command grep -q 'PR-WATCH IDENTITY UNKNOWN' "$LOG_FILE" \
    || fail "unverifiable pr-watch identity was not reported"
)
