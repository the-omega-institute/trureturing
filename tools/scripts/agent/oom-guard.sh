#!/usr/bin/env bash
# Ensure the single module known to peak host memory (#6360) is already built in
# a lane before any Lean build runs there. Copies artifacts from a donor lane
# that has them, but only when the source bytes match exactly.
#
# The copy is a plain one: the repository forbids per-file clone walks, and the
# artifacts of this one module measure two megabytes together, so a clone would
# buy nothing. LC_ALL is pinned because shasum is a Perl program on Darwin.
#
# What counts as this module's artifacts is a rule, not a list: every file under
# the two build subtrees whose name is the module's own name followed by a dot.
# A fixed extension table gets this wrong in both directions — the one it carried
# named .c.trace, which lake does not write here, and omitted .setup.json, which
# it writes for every module.
#
# Usage: oom-guard.sh <lane-dir> [donor-dir ...]
# Exit 0 when the lane is safe to build; 2 when it is not and no donor could fix it.
set -u
export LC_ALL=C

MODULE="D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree"
LANE="${1:?usage: oom-guard.sh <lane-dir> [donor-dir ...]}"
shift || true
DONORS=("$@")
if [ "${#DONORS[@]}" -eq 0 ]; then
  DONORS=(/Users/chronoai/trureturing /Users/chronoai/trureturing-prime-a \
          /Users/chronoai/trureturing-prime-b /Users/chronoai/trureturing-prime-c)
fi

target="$LANE/.lake/build/lib/lean/$MODULE.olean"
if [ -f "$target" ]; then
  echo "OOM_GUARD lane=$LANE status=present donor=none"
  exit 0
fi
if [ ! -f "$LANE/$MODULE.lean" ]; then
  echo "OOM_GUARD lane=$LANE status=no-source"
  exit 0
fi
want=$(shasum -a 256 "$LANE/$MODULE.lean" | awk '{print $1}')

for d in "${DONORS[@]}"; do
  [ "$d" = "$LANE" ] && continue
  [ -f "$d/.lake/build/lib/lean/$MODULE.olean" ] || continue
  [ -f "$d/$MODULE.lean" ] || continue
  got=$(shasum -a 256 "$d/$MODULE.lean" | awk '{print $1}')
  [ "$got" = "$want" ] || continue
  base="${MODULE##*/}"
  dir="${MODULE%/*}"
  n=0
  for sub in lib/lean ir; do
    sdir="$d/.lake/build/$sub/$dir"
    ddir="$LANE/.lake/build/$sub/$dir"
    for src in "$sdir/$base".*; do
      [ -f "$src" ] || continue
      mkdir -p "$ddir" || continue
      cp "$src" "$ddir/${src##*/}" 2>/dev/null && n=$((n+1))
    done
  done
  echo "OOM_GUARD lane=$LANE status=seeded donor=$d files=$n sha=$want"
  exit 0
done

echo "OOM_GUARD lane=$LANE status=NO-DONOR sha=$want"
exit 2
