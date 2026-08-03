#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C
export LANG=C

readonly REPOSITORY_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd -P)"
readonly SCRIPT_UNDER_TEST="$REPOSITORY_ROOT/.fkst/scripts/run.sh"

fail() {
  printf 'FAIL startup-graphql-budget: %s\n' "$*" >&2
  exit 1
}

make_fixture() {
  local root="$1" probe_mode="$2" reset="$3"
  mkdir -p "$root/operate" "$root/checkout/.fkst" "$root/checkout/.git" \
    "$root/platform/scripts" "$root/bin" "$root/durable" "$root/runtime"
  cp "$REPOSITORY_ROOT/.fkst/substrate-ref" "$root/checkout/.fkst/substrate-ref"
  cp "$REPOSITORY_ROOT/.fkst/fkst.lock" "$root/checkout/.fkst/fkst.lock"
  cp "$REPOSITORY_ROOT/.fkst/fkst.workspace.toml" "$root/checkout/.fkst/fkst.workspace.toml"
  mkdir -p "$root/checkout/packages"

  cat >"$root/operate/host.env" <<EOF
BIN=/usr/bin/true
FKST_PLATFORM_ROOT=$root/platform
FKST_GITHUB_REPO=the-omega-institute/trureturing
FKST_HOST_ROOT=$root/checkout
FKST_DURABLE_ROOT=$root/durable
FKST_RUNTIME_ROOT=$root/runtime
EOF

  cat >"$root/bin/gh" <<'EOF'
#!/usr/bin/env bash
printf 'gh %s\n' "$*" >>"$EVENTS"
[[ "$*" == "api rate_limit --jq .resources.graphql | [.limit, .remaining, .reset] | @tsv" ]] \
  || exit 64
case "$PROBE_MODE" in
  low) printf '5000\t999\t%s\n' "$RESET_EPOCH" ;;
  failure) printf 'probe unavailable\n' >&2; exit 2 ;;
  malformed) printf '5000\tnot-a-number\t%s\n' "$RESET_EPOCH" ;;
  *) exit 65 ;;
esac
EOF
  chmod +x "$root/bin/gh"

  cat >"$root/bin/sleep" <<'EOF'
#!/usr/bin/env bash
printf 'sleep %s\n' "$1" >>"$EVENTS"
EOF
  chmod +x "$root/bin/sleep"

  cat >"$root/platform/scripts/run.sh" <<'EOF'
#!/usr/bin/env bash
printf 'platform %s\n' "$*" >>"$EVENTS"
printf '%s\n' "$$" >"$PLATFORM_PID_FILE"
exec /bin/sleep 3
EOF
  chmod +x "$root/platform/scripts/run.sh"

  export EVENTS="$root/events"
  export PLATFORM_PID_FILE="$root/platform.pid"
  export PROBE_MODE="$probe_mode"
  export RESET_EPOCH="$reset"
  export FKST_OPERATE_ROOT="$root/operate"
  export PATH="$root/bin:$ORIGINAL_PATH"
}

run_low_budget_case() (
  local root reset output delay gh_line sleep_line platform_line
  root="$(mktemp -d "${TMPDIR:-/tmp}/startup-graphql-budget-low.XXXXXX")"
  root="$(cd -- "$root" && pwd -P)"
  trap '[[ ! -f "$PLATFORM_PID_FILE" ]] || kill "$(cat "$PLATFORM_PID_FILE")" 2>/dev/null || true; rm -rf -- "$root"' EXIT
  reset=$(($(date +%s) + 30))
  make_fixture "$root" low "$reset"
  output="$root/output"

  "$SCRIPT_UNDER_TEST" supervise >"$output" 2>&1 \
    || fail "low-budget supervise exited nonzero: $(cat "$output")"
  grep -Fq "remaining=999" "$output" || fail "low-budget output omitted remaining"
  grep -Fq "limit=5000" "$output" || fail "low-budget output omitted limit"
  grep -Fq "reset=$reset" "$output" || fail "low-budget output omitted reset"

  gh_line="$(grep -n '^gh ' "$EVENTS" | cut -d: -f1)"
  sleep_line="$(grep -n '^sleep ' "$EVENTS" | head -1 | cut -d: -f1)"
  platform_line="$(grep -n '^platform ' "$EVENTS" | cut -d: -f1)"
  [[ -n "$gh_line" && -n "$sleep_line" && -n "$platform_line" ]] \
    || fail "probe, delay, or platform event missing: $(cat "$EVENTS")"
  [[ "$gh_line" -lt "$sleep_line" && "$sleep_line" -lt "$platform_line" ]] \
    || fail "platform started before the budget delay: $(cat "$EVENTS")"
  delay="$(sed -n "${sleep_line}s/^sleep //p" "$EVENTS")"
  [[ "$delay" =~ ^[1-9][0-9]*$ ]] || fail "reset delay was not positive: $delay"
  grep -Fq "platform supervise --project-root $root/checkout --platform-root $root/platform" "$EVENTS" \
    || fail "platform supervise command changed: $(cat "$EVENTS")"
)

run_rejection_case() (
  local mode="$1" expected="$2" root reset output status
  root="$(mktemp -d "${TMPDIR:-/tmp}/startup-graphql-budget-reject.XXXXXX")"
  root="$(cd -- "$root" && pwd -P)"
  trap 'rm -rf -- "$root"' EXIT
  reset=$(($(date +%s) + 30))
  make_fixture "$root" "$mode" "$reset"
  output="$root/output"

  set +e
  "$SCRIPT_UNDER_TEST" supervise >"$output" 2>&1
  status=$?
  set -e
  [[ "$status" -ne 0 ]] || fail "$mode probe unexpectedly started supervise"
  grep -Fq "$expected" "$output" \
    || fail "$mode probe diagnostic mismatch (exit=$status): $(cat "$output")"
  ! grep -q '^platform ' "$EVENTS" \
    || fail "$mode probe launched platform: $(cat "$EVENTS")"
)

ORIGINAL_PATH="$PATH"
run_low_budget_case
printf '%s\n' 'PASS startup-graphql-budget delays low-budget supervise before launch'
run_rejection_case failure 'fkst: GraphQL rate-limit probe failed'
printf '%s\n' 'PASS startup-graphql-budget rejects failed probe without launch'
run_rejection_case malformed 'fkst: GraphQL rate-limit probe returned malformed fields'
printf '%s\n' 'PASS startup-graphql-budget rejects malformed probe without launch'
