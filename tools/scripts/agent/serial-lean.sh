#!/usr/bin/env bash
set -u
export LC_ALL=C

fail() { echo "SERIAL_LEAN status=error built=0 failed=0 missing=0 tree=${TREE:-none} reason=$1"; exit 2; }

TREE="${1:-$(pwd)}"
[[ -d "$TREE" ]] || fail "no-such-tree"
TREE="$(cd "$TREE" && pwd -P)"
BUDGET="${2:-1200}"
case "$BUDGET" in ''|*[!0-9]*) fail "timeout-not-a-number" ;; esac
make -C "$TREE" lean-cache-ensure || fail "ensure-failed"


lake_runner="$TREE/tools/scripts/worktree/lean-cache-run.sh"
[ -x "$lake_runner" ] || fail "no-cache-runner"

missing=$(comm -23 \
  <(git -C "$TREE" ls-tree -r --name-only HEAD D5 | grep '\.lean$' \
      | sed 's|^D5/||; s|\.lean$||' | sort) \
  <(cd "$TREE/.lake/build/lib/lean/D5" 2>/dev/null && find . -name '*.olean' \
      | sed 's|^\./||; s|\.olean$||' | sort))

count=$(printf '%s' "$missing" | grep -c . || true)

built=0; failed=0
while IFS= read -r stem; do
  [ -n "$stem" ] || continue
  if ( cd "$TREE" && timeout "$BUDGET" "$lake_runner" lake build "D5/$stem.lean" ) >/dev/null 2>&1; then
    built=$((built+1))
  else
    failed=$((failed+1)); echo "SERIAL_LEAN_FAILED module=D5/$stem.lean"
  fi
done <<< "$missing"

stale_built=0; passes=0
while :; do
  passes=$((passes+1))
  if [ "$passes" -gt 200 ]; then
    failed=$((failed+1)); echo "SERIAL_LEAN_FAILED stale-targets-did-not-converge passes=$passes"; break
  fi
  stale=$(cd "$TREE" && "$lake_runner" lake build --no-build 2>&1 | grep '^- ' | sed 's/^- //' || true)
  [ -n "$stale" ] || break
  pass_built=0
  while IFS= read -r target; do
    [ -n "$target" ] || continue
    if ( cd "$TREE" && timeout "$BUDGET" "$lake_runner" lake build "$target" ) >/dev/null 2>&1; then
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
