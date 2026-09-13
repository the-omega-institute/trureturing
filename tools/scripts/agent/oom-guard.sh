#!/usr/bin/env bash
# Ensure the modules known to peak host memory are already built in a lane before
# any Lean build runs there. Copies artifacts from a donor lane that has them,
# but only when the source bytes match exactly.
#
# The copy is a plain one: the repository forbids per-file clone walks, and the
# artifacts of these modules measure a few megabytes together, so a clone would
# buy nothing. LC_ALL is pinned because shasum is a Perl program on Darwin.
#
# What counts as a module's artifacts is a rule, not a list: every file under
# the two build subtrees whose name is the module's own name followed by a dot.
# A fixed extension table gets this wrong in both directions — the one it carried
# named .c.trace, which lake does not write here, and omitted .setup.json, which
# it writes for every module.
#
# **There is more than one culprit.** This script once seeded a single module and
# its comment called that one "the single module known to peak host memory". That
# was measured for #6360 and then went stale without any signal: a lane seeded by
# this guard was still killed by the host's low-memory watchdog. Measured
# 2026-09-11 with `/usr/bin/time -l lake env lean`, one process at a time:
#
#   D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree   #6360
#   D5/S0/Certificates/Games/VersionBOddCountUnderdetermines       7.57 GB peak
#
# A second entry cost one line. Believing the first one was alone cost seven
# consecutive kills. Add a module here whenever one is measured above ~4 GB;
# do not re-derive the claim that the list is complete.
#
# Donors are discovered, not listed. The previous version defaulted to four fixed
# paths (`trureturing-prime-{a,b,c}` and the main checkout); three of those four
# had already been removed, so the default donor set was effectively one entry
# and a lane with no donor reported NO-DONOR while a dozen warm trees sat next to
# it. Registered worktrees are the authority (第 4.2 条: the address is computed,
# not written down).
#
# Usage: oom-guard.sh <lane-dir> [donor-dir ...]
# Sentinel: OOM_GUARD lane=<dir> status=<ok|incomplete> seeded=<n> present=<n> absent-source=<n> missing=<n>
# Exit 0 when the lane is safe to build; 2 when some module is still missing and
# no donor could supply it.
set -u
export LC_ALL=C

MODULES=(
  D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree
  D5/S0/Certificates/Games/VersionBOddCountUnderdetermines
)

LANE="${1:?usage: oom-guard.sh <lane-dir> [donor-dir ...]}"
shift || true
[ -d "$LANE" ] || { echo "OOM_GUARD lane=$LANE status=incomplete seeded=0 present=0 absent-source=0 missing=0 reason=no-such-lane"; exit 2; }
DONORS=("$@")
if [ "${#DONORS[@]}" -eq 0 ]; then
  # Every registered worktree of this lane's repository, warmest-looking first is
  # not knowable here, so order is git's; the sha check below rejects wrong bytes.
  while IFS= read -r d; do
    [ -n "$d" ] && DONORS+=("$d")
  done < <(git -C "$LANE" worktree list --porcelain 2>/dev/null \
           | awk '/^worktree /{print substr($0,10)}')
fi

seed_one() {
  local module="$1" target want d got base dir sub sdir ddir src n
  target="$LANE/.lake/build/lib/lean/$module.olean"
  [ -f "$target" ] && { echo "  present $module"; return 0; }
  [ -f "$LANE/$module.lean" ] || { echo "  absent-source $module"; return 3; }
  want=$(shasum -a 256 "$LANE/$module.lean" | awk '{print $1}')
  for d in "${DONORS[@]}"; do
    [ "$d" = "$LANE" ] && continue
    [ -f "$d/.lake/build/lib/lean/$module.olean" ] || continue
    [ -f "$d/$module.lean" ] || continue
    got=$(shasum -a 256 "$d/$module.lean" | awk '{print $1}')
    [ "$got" = "$want" ] || continue
    base="${module##*/}"; dir="${module%/*}"; n=0
    for sub in lib/lean ir; do
      sdir="$d/.lake/build/$sub/$dir"; ddir="$LANE/.lake/build/$sub/$dir"
      for src in "$sdir/$base".*; do
        [ -f "$src" ] || continue
        mkdir -p "$ddir" || continue
        cp "$src" "$ddir/${src##*/}" 2>/dev/null && n=$((n+1))
      done
    done
    echo "  seeded $module donor=$d files=$n sha=$want"
    return 1
  done
  echo "  MISSING $module sha=$want"
  return 2
}

present=0; seeded=0; missing=0; absent=0
for m in "${MODULES[@]}"; do
  seed_one "$m"
  case $? in
    0) present=$((present + 1)) ;;
    1) seeded=$((seeded + 1)) ;;
    3) absent=$((absent + 1)) ;;
    *) missing=$((missing + 1)) ;;
  esac
done

if [ "$missing" -gt 0 ]; then
  echo "OOM_GUARD lane=$LANE status=incomplete seeded=$seeded present=$present absent-source=$absent missing=$missing"
  exit 2
fi
echo "OOM_GUARD lane=$LANE status=ok seeded=$seeded present=$present absent-source=$absent missing=0"
exit 0
