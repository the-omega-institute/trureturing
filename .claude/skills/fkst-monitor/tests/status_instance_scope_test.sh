#!/usr/bin/env bash
# Regression test for status.sh instance-scoping of the fatal/ack counters.
#
# The launchd supervise log is append-only ACROSS engine restarts. A fatal line from a prior
# instance — e.g. `[framework] startup error: ... integer 1800 ...`, a bug fixed by PR #357 and
# gone three restarts ago — must NOT mark the LIVE engine DOWN. status.sh must count only the
# current instance (from the last boot marker onward). This test builds a synthetic accumulated
# log with a pre-boot fatal + a boot marker + a clean current instance, and asserts:
#   - scope_log() slices from the boot marker (pre-boot fatal is excluded)
#   - the scoped fatal count is 0 and the scoped ack count reflects only the live instance
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
STATUS_SH="$SCRIPT_DIR/../scripts/status.sh"

fail() { echo "FAIL: $1" >&2; exit 1; }

# Source status.sh for its helpers. The dispatch case must be guarded so sourcing is inert.
# shellcheck disable=SC1090
source "$STATUS_SH"
# status.sh sets `set -euo pipefail`; sourcing imposes it on us. This test drives its own
# control flow via explicit `|| fail` / `&& fail`, and intentionally runs `grep -ac` that
# returns 1 on zero matches (the PASS condition) — under errexit+pipefail that would abort.
set +euo pipefail
type scope_log >/dev/null 2>&1 || fail "status.sh must expose scope_log() and be sourceable (guard the dispatch case)"

tmp="$(mktemp -t fkst-monitor-fixture.XXXXXX)"
cleanup() { rm -f "$tmp" "${INSTANCE_SLICE:-}"; }
trap cleanup EXIT

cat > "$tmp" <<'LOG'
TIMESTAMP=2026-07-22T18:00:00Z LEVEL=INFO package_roots=["/prior/instance"] MSG=compose
TIMESTAMP=2026-07-22T18:00:01Z LEVEL=INFO MSG=delivery acked
[framework] startup error: parse raisers/frontier_poll.lua: deserialize error: invalid type: integer `1800`, expected a string
TIMESTAMP=2026-07-22T18:00:03Z LEVEL=FATAL MSG=prior instance died
exec: /opt/synthetic/fkst-framework supervise --project-root /opt/synthetic/checkout --package-root /opt/synthetic/packages
TIMESTAMP=2026-07-22T19:46:16Z LEVEL=INFO package_roots=["/live/instance"] MSG=compose
TIMESTAMP=2026-07-22T19:46:17Z LEVEL=INFO dept=theory-selfgrowth.propose MSG=consumer started
TIMESTAMP=2026-07-22T19:46:40Z LEVEL=INFO MSG=delivery acked
TIMESTAMP=2026-07-22T19:47:00Z LEVEL=INFO MSG=delivery acked
LOG

# --- scope_log slices from the LAST boot marker ---
slice="$(scope_log "$tmp")"
[[ -f "$slice" ]] || fail "scope_log did not produce a slice file"
grep -q '/live/instance' "$slice" || fail "slice must include the live instance"
grep -q '/prior/instance' "$slice" && fail "slice must NOT include the prior (pre-boot) instance"

# --- the pre-boot fatals are excluded ---
fatal_scoped="$(awk 'length<1000' "$slice" | grep -acE 'LEVEL=FATAL|thread .main. panicked|panicked at |\[framework\] startup error|SIGSEGV|SIGABRT' | tr -dc '0-9')"
[[ "${fatal_scoped:-0}" == "0" ]] || fail "scoped fatal count must be 0, got '${fatal_scoped}' (pre-boot fatals leaked in)"

# --- contrast: the UNSCOPED whole-log count would (wrongly) be >0 ---
fatal_full="$(awk 'length<1000' "$tmp" | grep -acE 'LEVEL=FATAL|thread .main. panicked|panicked at |\[framework\] startup error|SIGSEGV|SIGABRT' | tr -dc '0-9')"
(( ${fatal_full:-0} >= 2 )) || fail "fixture sanity: whole-log fatal count should be >=2, got '${fatal_full}'"

# --- acks reflect only the live instance (2, not 3) ---
acks_scoped="$(grep -acE 'MSG=delivery acked' "$slice" | tr -dc '0-9')"
[[ "${acks_scoped:-0}" == "2" ]] || fail "scoped ack count must be 2 (live only), got '${acks_scoped}'"

echo "PASS: status.sh instance-scoping excludes pre-boot fatals ($fatal_full whole-log -> $fatal_scoped scoped) and scopes acks ($acks_scoped)"
