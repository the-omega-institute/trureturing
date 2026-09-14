#!/usr/bin/env bash
# Build the modules a tree is missing, one at a time, so the peak is bounded.
#
# `make lean` hands the whole target to lake, which picks its own parallelism
# from the core count. There is no knob to lower it: lake 4.33 has no -j and
# reads no environment variable for it — `lake build -j 1` answers "unknown
# short option '-j'", and the repository has no LEAN_NUM_THREADS anywhere
# (CLAUDE.md 第 10.1 条 records the same zero-hit grep). On an eight-core,
# 16 GB host that means seven concurrent lean processes holding 0.47 to 3.38 GB
# each; measured on 2026-09-09 the host's free memory fell to 10 MB and the
# compressor took 7 GB, and three separate `make lean` runs were killed by the
# host's low-memory guard — one of them with nothing else running.
#
# Invoking lake once per module pins the concurrency at one. The same tree that
# had just lost three parallel builds finished its remaining ten modules this
# way with zero failures.
#
# It is for the endgame, not the whole build: it computes what is missing and
# builds exactly that. Whether it beats "run make lean and hope" when hundreds
# of modules are missing is untested.
#
# Usage: serial-lean.sh [tree] [per-module-timeout-seconds]
# Sentinel: SERIAL_LEAN status=<complete|partial|error> built=<n> failed=<n> missing=<n> tree=<dir>
# Exit 0 when nothing is left to build, 1 when some module failed, 2 when it
# could not run.
set -u
export LC_ALL=C

fail() { echo "SERIAL_LEAN status=error built=0 failed=0 missing=0 tree=${TREE:-none} reason=$1"; exit 2; }

TREE="${1:-$(pwd)}"
BUDGET="${2:-1200}"
case "$BUDGET" in ''|*[!0-9]*) fail "timeout-not-a-number" ;; esac
[ -d "$TREE/.lake/build/lib/lean/D5" ] || fail "no-build-tree"

# 第 8.3 条: a bare lake on a tree without the cache stamp forfeits its clonefile
# donor and buys a full rebuild. Only a stamped, already-hot tree may be driven
# directly; anything else goes through the canonical ensure door first.
[ -f "$TREE/.lake/.stratalint-lean-cache-stamp.json" ] || fail "no-cache-stamp-run-lean-cache-ensure-first"

lake_bin="$(command -v lake || echo "$HOME/.elan/bin/lake")"
[ -x "$lake_bin" ] || fail "no-lake"

missing=$(comm -23 \
  <(git -C "$TREE" ls-tree -r --name-only HEAD D5 | grep '\.lean$' \
      | sed 's|^D5/||; s|\.lean$||' | sort) \
  <(cd "$TREE/.lake/build/lib/lean/D5" && find . -name '*.olean' \
      | sed 's|^\./||; s|\.olean$||' | sort))

count=$(printf '%s' "$missing" | grep -c . || true)

built=0; failed=0
while IFS= read -r stem; do
  [ -n "$stem" ] || continue
  if ( cd "$TREE" && timeout "$BUDGET" "$lake_bin" build "D5/$stem.lean" ) >/dev/null 2>&1; then
    built=$((built+1))
  else
    failed=$((failed+1)); echo "SERIAL_LEAN_FAILED module=D5/$stem.lean"
  fi
done <<< "$missing"

# Phase 2: lake's own staleness. Phase 1 only knows D5 oleans that are absent; a
# plain `lake build` (which `make lean-report` runs unconditionally, with lake's
# full parallelism) also rebuilds the `Trureturing` root, the LeanInformationAudit
# library and its tests, and any module whose trace no longer matches. Measured
# 2026-09-12 on a lane seeded from a donor behind dev: phase 1 reported nothing
# missing while `lake build` still started eight lean processes. `lake build
# --no-build` lists those targets without building them; build each alone.
# The query names the first stale leaf on each path, so a deep dependency chain
# surfaces one layer per pass (measured 2026-09-12: 11, 62, 28, ... targets per
# pass, 169 targets over six passes on a freshly seeded lane). Passes are
# bounded only by progress: a pass that builds nothing while the list is still
# non-empty is a real failure, not a slow convergence.
stale_built=0; passes=0
while :; do
  passes=$((passes+1))
  if [ "$passes" -gt 200 ]; then
    failed=$((failed+1)); echo "SERIAL_LEAN_FAILED stale-targets-did-not-converge passes=$passes"; break
  fi
  stale=$(cd "$TREE" && "$lake_bin" build --no-build 2>&1 | grep '^- ' | sed 's/^- //' || true)
  [ -n "$stale" ] || break
  pass_built=0
  while IFS= read -r target; do
    [ -n "$target" ] || continue
    if ( cd "$TREE" && timeout "$BUDGET" "$lake_bin" build "$target" ) >/dev/null 2>&1; then
      stale_built=$((stale_built+1)); pass_built=$((pass_built+1))
    else
      failed=$((failed+1)); echo "SERIAL_LEAN_FAILED target=$target"
    fi
  done <<< "$stale"
  if [ "$pass_built" -eq 0 ]; then
    failed=$((failed+1)); echo "SERIAL_LEAN_FAILED stale-targets-made-no-progress pass=$passes"; break
  fi
done

if [ "$failed" -eq 0 ]; then
  echo "SERIAL_LEAN status=complete built=$built failed=0 missing=$count stale_built=$stale_built tree=$TREE"; exit 0
fi
echo "SERIAL_LEAN status=partial built=$built failed=$failed missing=$count stale_built=$stale_built tree=$TREE"
exit 1
