#!/usr/bin/env bash
# Bring the clonefile donor up to the build state of the fullest worktree.
#
# `make worktree` seeds a new lane by cloning the main checkout's .lake. When the
# main checkout is behind on built modules, every new lane inherits that hole and
# rebuilds it on first Lean target — which is how one 16GB module (#6360) came to
# be rebuilt over and over. oom-guard.sh seeds that one module; this seeds the
# whole difference, which is the actual shape of the problem: on 2026-09-09 the
# donor held 3552 project oleans against 3855 in the fullest lane, a hole of 303.
#
# Only worktrees on the same commit are eligible as sources: identical HEAD means
# identical Lean sources, which is what makes the artifacts interchangeable. The
# copy is plain — the repository forbids per-file clone walks — and skips any file
# already present, so it is idempotent and never overwrites.
#
# What counts as a module's artifacts is a rule, not a list: every file under the
# two build subtrees whose name is the module's own name followed by a dot. Most
# modules have five such files beside the olean and three beside the C output, but
# one in this tree also carries .olean.private, .olean.server and .ir.sig, so a
# fixed extension table would silently copy such a module in half.
#
# Usage: donor-backfill.sh [--dry-run] [donor-dir]
# Sentinel: DONOR_BACKFILL status=<synced|seeded|no-source|behind> donor=<n> best=<n> copied=<files>
# Exit 0 when the donor is at or brought to the fullest state; 2 when no eligible
# source exists.
set -u
export LC_ALL=C

DRY=0
if [ "${1:-}" = "--dry-run" ]; then DRY=1; shift; fi
DONOR="${1:-/Users/chronoai/trureturing}"

if [ ! -d "$DONOR/.git" ] && [ ! -f "$DONOR/.git" ]; then
  echo "DONOR_BACKFILL status=no-source donor=0 best=0 copied=0 reason=not-a-worktree"
  exit 2
fi

donor_head=$(git -C "$DONOR" rev-parse HEAD 2>/dev/null) || {
  echo "DONOR_BACKFILL status=no-source donor=0 best=0 copied=0 reason=no-head"
  exit 2
}

count_oleans() {
  find "$1/.lake/build/lib/lean/D5" -name '*.olean' 2>/dev/null | wc -l | tr -d ' '
}

donor_n=$(count_oleans "$DONOR")

# Pick the fullest worktree that sits on the donor's commit.
best=""
best_n="$donor_n"
while read -r w; do
  [ -n "$w" ] || continue
  [ "$w" = "$DONOR" ] && continue
  h=$(git -C "$w" rev-parse HEAD 2>/dev/null) || continue
  [ "$h" = "$donor_head" ] || continue
  n=$(count_oleans "$w")
  if [ "$n" -gt "$best_n" ]; then best="$w"; best_n="$n"; fi
done < <(git -C "$DONOR" worktree list --porcelain | awk '/^worktree /{print substr($0,10)}')

if [ -z "$best" ]; then
  echo "DONOR_BACKFILL status=synced donor=$donor_n best=$donor_n copied=0"
  exit 0
fi

if [ "$DRY" -eq 1 ]; then
  echo "DONOR_BACKFILL status=behind donor=$donor_n best=$best_n copied=0 source=$best"
  exit 0
fi

copied=0
while read -r rel; do
  [ -n "$rel" ] || continue
  stem="${rel%.olean}"
  base="${stem##*/}"
  dir="${stem%/*}"
  [ "$dir" = "$stem" ] && dir="."
  for sub in "lib/lean/D5" "ir/D5"; do
    sdir="$best/.lake/build/$sub/$dir"
    ddir="$DONOR/.lake/build/$sub/$dir"
    for src in "$sdir/$base".*; do
      [ -f "$src" ] || continue
      dst="$ddir/${src##*/}"
      [ -f "$dst" ] && continue
      mkdir -p "$ddir" || continue
      cp "$src" "$dst" 2>/dev/null && copied=$((copied+1))
    done
  done
done < <(cd "$best/.lake/build/lib/lean/D5" 2>/dev/null && find . -name '*.olean' | sed 's|^\./||')

after=$(count_oleans "$DONOR")
echo "DONOR_BACKFILL status=seeded donor=$after best=$best_n copied=$copied source=$best"
exit 0
