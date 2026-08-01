# Checkout-synchronization cases sourced by hourly-maintenance-behavior.sh.

checkout_fast_forwards_only_clean_ancestors() (
  load_implementation || exit 1
  local root
  root="$(mktemp -d -t hourly-maintenance-clean-ancestor.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  mkdir -p "$root/logs"
  LOG_FILE="$root/logs/hourly-maintenance.log"
  export FKST_MAINTENANCE_LOG="$LOG_FILE"
  create_checkout_history_fixture "$root" || exit 1
  advance_checkout_dev first || exit 1
  export FKST_HOST_ROOT="$CHECKOUT_ROOT"

  sync_checkout || fail "clean ancestor sync should be nonfatal"
  [[ "$(command git -C "$CHECKOUT_ROOT" rev-parse HEAD)" == "$CHECKOUT_DEV_REV" ]] \
    || fail "clean ancestor did not fast-forward"

  advance_checkout_dev second || exit 1
  printf 'dirty\n' >> "$CHECKOUT_ROOT/tracked"
  local dirty_head
  dirty_head="$(command git -C "$CHECKOUT_ROOT" rev-parse HEAD)"
  sync_checkout || fail "dirty ancestor refusal should be nonfatal"
  [[ "$(command git -C "$CHECKOUT_ROOT" rev-parse HEAD)" == "$dirty_head" ]] \
    || fail "dirty ancestor was changed"
  command grep -q 'CHECKOUT-FF-BLOCKED' "$LOG_FILE" \
    || fail "dirty ancestor refusal was not reported"
)

checkout_untracked_files_do_not_block_fast_forward() (
  load_implementation || exit 1
  local root
  root="$(mktemp -d -t hourly-maintenance-untracked-ff.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  mkdir -p "$root/logs"
  LOG_FILE="$root/logs/hourly-maintenance.log"
  export FKST_MAINTENANCE_LOG="$LOG_FILE"
  create_checkout_history_fixture "$root" || exit 1
  advance_checkout_dev first || exit 1
  export FKST_HOST_ROOT="$CHECKOUT_ROOT"

  # Untracked files provably do not prevent a fast-forward: git merge --ff-only
  # succeeds with them present. Intentional host-local files such as the
  # Spotlight-exclusion marker must not freeze deployment.
  printf 'litter
' > "$CHECKOUT_ROOT/runtime.note"
  printf '' > "$CHECKOUT_ROOT/.metadata_never_index"

  sync_checkout || fail "untracked-only checkout sync should be nonfatal"
  [[ "$(command git -C "$CHECKOUT_ROOT" rev-parse HEAD)" == "$CHECKOUT_DEV_REV" ]]     || fail "untracked files blocked the fast-forward"
  command grep -q 'CHECKOUT-FF-BLOCKED' "$LOG_FILE"     && fail "untracked files were reported as uncommitted changes"

  # the untracked files must survive the fast-forward untouched
  [[ -f "$CHECKOUT_ROOT/runtime.note" ]]     || fail "fast-forward destroyed an untracked host file"
  [[ -f "$CHECKOUT_ROOT/.metadata_never_index" ]]     || fail "fast-forward destroyed the Spotlight marker"

  # a TRACKED modification must still block, so the guard is not simply removed
  advance_checkout_dev second || exit 1
  printf 'dirty
' >> "$CHECKOUT_ROOT/tracked"
  local dirty_head
  dirty_head="$(command git -C "$CHECKOUT_ROOT" rev-parse HEAD)"
  sync_checkout || fail "tracked-dirty refusal should be nonfatal"
  [[ "$(command git -C "$CHECKOUT_ROOT" rev-parse HEAD)" == "$dirty_head" ]]     || fail "tracked-dirty checkout was advanced"
  command grep -q 'CHECKOUT-FF-BLOCKED' "$LOG_FILE"     || fail "tracked-dirty refusal was not reported"
)

checkout_divergence_refuses_auto_fast_forward() (
  load_implementation || exit 1
  local root
  root="$(mktemp -d -t hourly-maintenance-diverged.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  mkdir -p "$root/logs"
  LOG_FILE="$root/logs/hourly-maintenance.log"
  export FKST_MAINTENANCE_LOG="$LOG_FILE"
  create_checkout_history_fixture "$root" || exit 1
  advance_checkout_dev remote || exit 1
  printf 'local\n' > "$CHECKOUT_ROOT/local-only"
  command git -C "$CHECKOUT_ROOT" add local-only
  git_quiet -C "$CHECKOUT_ROOT" commit -m local || exit 1
  local local_head
  local_head="$(command git -C "$CHECKOUT_ROOT" rev-parse HEAD)"
  export FKST_HOST_ROOT="$CHECKOUT_ROOT"

  sync_checkout || fail "divergence refusal should be nonfatal"
  [[ "$(command git -C "$CHECKOUT_ROOT" rev-parse HEAD)" == "$local_head" ]] \
    || fail "diverged checkout was silently reset"
  command grep -q 'CHECKOUT DIVERGED' "$LOG_FILE" \
    || fail "divergence refusal was not reported"
)

checkout_status_failure_refuses_auto_fast_forward() (
  load_implementation || exit 1
  local root
  root="$(mktemp -d -t hourly-maintenance-status-failure.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  mkdir -p "$root/bin" "$root/logs"
  LOG_FILE="$root/logs/hourly-maintenance.log"
  export FKST_MAINTENANCE_LOG="$LOG_FILE"
  create_checkout_history_fixture "$root" || exit 1
  advance_checkout_dev remote || exit 1
  export FKST_HOST_ROOT="$CHECKOUT_ROOT"
  local real_git before
  real_git="$(command -v git)"
  before="$(command git -C "$CHECKOUT_ROOT" rev-parse HEAD)"
  cat > "$root/bin/git" <<SH
#!/usr/bin/env bash
if [[ "\$*" == *" status --porcelain "* ]]; then exit 9; fi
exec "$real_git" "\$@"
SH
  chmod +x "$root/bin/git"
  export PATH="$root/bin:$PATH"

  sync_checkout || fail "checkout inspection failure should be nonfatal"
  [[ "$(command git -C "$CHECKOUT_ROOT" rev-parse HEAD)" == "$before" ]] \
    || fail "checkout advanced after cleanliness inspection failed"
  command grep -q 'CHECKOUT-STATUS-FAIL' "$LOG_FILE" \
    || fail "checkout cleanliness inspection failure was not reported"
)

stale_deployed_repository_contract_does_not_block_checkout_refresh() (
  local root output checkout_remote checkout_writer stale_rev current_rev
  root="$(mktemp -d -t hourly-maintenance-contract-bootstrap.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  create_platform_fixture "$root" || exit 1
  write_host_contract_fixture "$root" second-host-bot integration-second-host
  output="$root/entrypoint.output"
  checkout_remote="$root/checkout-remote.git"
  checkout_writer="$root/checkout-writer"

  sed "s/^rev = \"[0-9a-f]*\"/rev = \"$NEW_PLATFORM_REV\"/" \
    "$FIXTURE_HOST_ROOT/.fkst/fkst.workspace.toml" \
    > "$FIXTURE_HOST_ROOT/fkst.workspace.toml"
  printf 'deployed-lock\n' > "$FIXTURE_HOST_ROOT/fkst.lock"
  printf 'FKST_GITHUB_BOT_LOGIN=stale-repository-copy\n' \
    >> "$FIXTURE_HOST_ROOT/.fkst/deploy.env"
  git_quiet init --bare --initial-branch=dev "$checkout_remote" || exit 1
  git_quiet -C "$FIXTURE_HOST_ROOT" init --initial-branch=dev || exit 1
  configure_repository "$FIXTURE_HOST_ROOT" || exit 1
  command git -C "$FIXTURE_HOST_ROOT" add .
  git_quiet -C "$FIXTURE_HOST_ROOT" commit -m stale-contract || exit 1
  git_quiet -C "$FIXTURE_HOST_ROOT" remote add origin "$checkout_remote" || exit 1
  git_quiet -C "$FIXTURE_HOST_ROOT" push -u origin dev || exit 1
  stale_rev="$(command git -C "$FIXTURE_HOST_ROOT" rev-parse HEAD)"

  git_quiet clone "$checkout_remote" "$checkout_writer" || exit 1
  configure_repository "$checkout_writer" || exit 1
  command cp "$REPOSITORY_ROOT/.fkst/deploy.env" "$checkout_writer/.fkst/deploy.env"
  command git -C "$checkout_writer" add .fkst/deploy.env
  git_quiet -C "$checkout_writer" commit -m current-contract || exit 1
  git_quiet -C "$checkout_writer" push origin dev || exit 1
  current_rev="$(command git -C "$checkout_writer" rev-parse HEAD)"
  [[ "$stale_rev" != "$current_rev" ]] || fail "stale checkout fixture did not advance"

  cat > "$root/bin/pgrep" <<'SH'
#!/usr/bin/env bash
printf '4242\n'
SH
  cat > "$root/bin/gh" <<'SH'
#!/usr/bin/env bash
[[ "$*" == *"issue list"* ]] || exit 8
printf '1\n'
SH
  cat > "$root/bin/make" <<'SH'
#!/usr/bin/env bash
exit 0
SH
  chmod +x "$root/bin/pgrep" "$root/bin/gh" "$root/bin/make"

  env -i HOME="$root/home" PATH="/usr/bin:/bin" \
    /bin/bash "$SCRIPT_UNDER_TEST" --host-config "$FIXTURE_HOST_CONFIG" \
    >"$output" 2>&1 \
    || fail "stale repository contract blocked maintenance: $(<"$output")"
  [[ "$(command git -C "$FIXTURE_HOST_ROOT" rev-parse HEAD)" == "$current_rev" ]] \
    || fail "maintenance did not refresh the stale checkout: $(<"$output")"
  ! command grep -q '^FKST_GITHUB_BOT_LOGIN=' "$FIXTURE_HOST_ROOT/.fkst/deploy.env" \
    || fail "refreshed checkout retained the stale host-owned repository key"
  command grep -q 'CHECKOUT BEHIND' "$output" \
    || fail "maintenance output did not record the checkout refresh: $(<"$output")"
)
