#!/usr/bin/env bash
# Regression test for diag_count reporting zero-count patterns instead of vanishing.
#
# `diag_count` captured its counters as `now="$(grep -acE "$pat" ...)"` under status.sh's
# `set -euo pipefail`. `grep -c` exits 1 on zero matches, so the FIRST pattern with no hits
# aborted the whole loop and every later pattern silently disappeared from the report.
#
# That is the worst possible failure mode for this particular tool: diag exists to answer
# "is X happening NOW", and its answer is carried by the contrast between a live pattern
# (current>0) and quiet ones (current=0). Dropping the quiet rows destroys the contrast and
# reads as "only the first thing is worth reporting".
#
# Note that the sibling instance-scope test already documented the `grep -ac` errexit hazard
# in its own preamble and worked around it locally with `set +euo pipefail` — the knowledge
# existed in a test comment while the production helper still had the bug. This test pins the
# property against the real helper so it cannot regress.
#
# Asserts, over a fixture where only some patterns match:
#   - every requested pattern appears in the output (none silently dropped)
#   - a zero-match pattern reports current=0 (not absent, not an error)
#   - a matching pattern still reports its true nonzero current count
#   - a zero-match pattern placed FIRST does not suppress later matching patterns
#
# Set STATUS_SH to point at an alternate copy (used to verify this test actually fails against
# the pre-fix helper); it defaults to the canonical script.
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
STATUS_SH="${STATUS_SH:-$SCRIPT_DIR/../scripts/status.sh}"

fail() { echo "FAIL: $1" >&2; exit 1; }

tmpdir="$(mktemp -d -t fkst-monitor-diag.XXXXXX)"
cleanup() { rm -rf "$tmpdir"; }
trap cleanup EXIT

# diag_count reads the newest supervise log from "$FKST_HOME/logs"; point FKST_HOME at a fixture.
mkdir -p "$tmpdir/logs"
cat > "$tmpdir/logs/supervise-launchd.log" <<'LOG'
TIMESTAMP=2026-07-29T18:00:00Z LEVEL=INFO package_roots=["/prior/instance"] MSG=compose
TIMESTAMP=2026-07-29T18:00:01Z LEVEL=error MSG=github-devloop error_class=caught-failure
exec: /x/fkst-substrate/target/debug/fkst-framework supervise --project-root /x/checkout --package-root /x
TIMESTAMP=2026-07-29T19:00:00Z LEVEL=INFO package_roots=["/live/instance"] MSG=compose
TIMESTAMP=2026-07-29T19:00:10Z LEVEL=INFO MSG=reconcile label issue/500/impl-failed
TIMESTAMP=2026-07-29T19:00:20Z LEVEL=INFO MSG=reconcile label issue/499/impl-failed
LOG

# A zero-match pattern FIRST, so a regression truncates everything after it.
out="$(FKST_HOME="$tmpdir" bash "$STATUS_SH" diag \
  'ZZZ-absent-pattern-ZZZ' 'impl-failed' 'panic' 'error_class' 2>&1)" \
  || fail "diag exited nonzero; output was: $out"

for pat in 'ZZZ-absent-pattern-ZZZ' 'impl-failed' 'panic' 'error_class'; do
  grep -q -- "$pat" <<<"$out" \
    || fail "pattern '$pat' is missing from the report (silently dropped). Output: $out"
done

row_for() { grep -- "^  $1 " <<<"$out" | head -1; }

# --- a zero-match pattern reports current=0, and does not suppress what follows ---
grep -q 'current=0' <<<"$(row_for 'ZZZ-absent-pattern-ZZZ')" \
  || fail "absent pattern must report current=0, got: $(row_for 'ZZZ-absent-pattern-ZZZ')"
grep -q 'current=0' <<<"$(row_for 'panic')" \
  || fail "'panic' has no matches and must report current=0, got: $(row_for 'panic')"

# --- a matching pattern still reports its true count, scoped to the live instance ---
grep -q 'current=2' <<<"$(row_for 'impl-failed')" \
  || fail "'impl-failed' must report current=2 (live instance only), got: $(row_for 'impl-failed')"

# --- instance scoping still holds: the pre-boot error_class is excluded from current, kept in full ---
row="$(row_for 'error_class')"
grep -q 'current=0' <<<"$row" \
  || fail "'error_class' occurs only pre-boot; current must be 0, got: $row"
grep -q 'full=1' <<<"$row" \
  || fail "'error_class' must still be counted in full history (full=1), got: $row"

echo "PASS: diag reports all 4 patterns; zero-count rows report current=0 without truncating the report"
