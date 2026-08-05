# Authority-checkout cases sourced by hourly-maintenance-behavior.sh.

authority_checkout_tracks_the_deployed_platform_pin() (
  load_implementation || exit 1
  local root authority_root dirty_head
  root="$(mktemp -d -t hourly-maintenance-authority.XXXXXX)" || exit 1
  trap 'rm -rf "$root"' EXIT
  mkdir -p "$root/logs"
  LOG_FILE="$root/logs/hourly-maintenance.log"
  export FKST_MAINTENANCE_LOG="$LOG_FILE"
  create_checkout_history_fixture "$root" || exit 1
  mkdir -p "$CHECKOUT_ROOT/packages/github-proxy"
  authority_root="$CHECKOUT_ROOT/packages/github-proxy"
  export FKST_GITHUB_PROXY_AUTHORITY_ROOT="$authority_root"

  advance_checkout_dev first || exit 1
  sync_authority_checkout "$CHECKOUT_DEV_REV" \
    || fail "clean authority ancestor sync should be nonfatal"
  [[ "$(command git -C "$authority_root" rev-parse HEAD)" == "$CHECKOUT_DEV_REV" ]] \
    || fail "clean authority checkout did not fast-forward to the deployed pin"

  : > "$LOG_FILE"
  sync_authority_checkout "$CHECKOUT_DEV_REV" \
    || fail "current authority checkout should be nonfatal"
  command grep -q 'AUTHORITY CURRENT' "$LOG_FILE" \
    || fail "current authority checkout was not reported as a no-op"

  printf 'dirty-current\n' >> "$CHECKOUT_ROOT/tracked"
  : > "$LOG_FILE"
  sync_authority_checkout "$CHECKOUT_DEV_REV" \
    || fail "dirty current authority refusal should be nonfatal"
  command grep -q 'AUTHORITY-FF-BLOCKED.*uncommitted changes' "$LOG_FILE" \
    || fail "dirty current authority refusal was not reported"
  command git -C "$CHECKOUT_ROOT" checkout -- tracked || exit 1

  advance_checkout_dev second || exit 1
  printf 'dirty\n' >> "$CHECKOUT_ROOT/tracked"
  dirty_head="$(command git -C "$authority_root" rev-parse HEAD)"
  : > "$LOG_FILE"
  sync_authority_checkout "$CHECKOUT_DEV_REV" \
    || fail "dirty authority refusal should be nonfatal"
  [[ "$(command git -C "$authority_root" rev-parse HEAD)" == "$dirty_head" ]] \
    || fail "dirty authority checkout was changed"
  command grep -q 'AUTHORITY-FF-BLOCKED.*uncommitted changes' "$LOG_FILE" \
    || fail "dirty authority refusal was not reported"
)
