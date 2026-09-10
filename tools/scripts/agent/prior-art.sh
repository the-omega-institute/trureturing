#!/usr/bin/env bash
# Prior-art probe: does this repository already have it?
#
# Run this BEFORE dispatching an implementation seat, not after. Rule 11 requires
# searching this repository's own D5 tree before formalising anything, and the
# expensive way to learn that is to discover the duplicate in the seat's report.
#
# Usage:
#   tools/scripts/agent/prior-art.sh <term> [<term> ...]
#
# Terms are matched case-insensitively. An arXiv identifier is a good term; so is
# the name of the object ("Foata", "unimodal", "parking function"). Give several.
#
# Searches, in order of how often each one has actually caught something:
#   1. origin/dev  — the frozen tree: D5, Blueprint, Library notes, theory volumes
#   2. open pull requests — titles and bodies
#   3. remote branches — lanes in flight that have not opened a PR yet
#
# Exit codes:
#   0  no hit anywhere; the target looks new
#   3  at least one hit; READ THEM before dispatching
#   2  bad usage or missing dependency

set -uo pipefail

die() { printf 'prior-art: %s\n' "$1" >&2; exit 2; }

[ "$#" -ge 1 ] || die "usage: prior-art.sh <term> [<term> ...]"
command -v git >/dev/null 2>&1 || die "git not found"
git rev-parse --git-dir >/dev/null 2>&1 || die "not inside a git repository"

REPO="${PRIOR_ART_REPO:-the-omega-institute/trureturing}"
BASE="${PRIOR_ART_BASE:-origin/dev}"

git rev-parse --verify --quiet "$BASE" >/dev/null || die "revision '$BASE' not found; fetch first"

hits=0

for term in "$@"; do
  printf '\n=== %s ===\n' "$term"

  printf -- '--- %s (D5 / Blueprint / Library / theory) ---\n' "$BASE"
  found=$(git grep -il -e "$term" "$BASE" -- \
            'D5/**' 'Blueprint/**' 'Library/**' 'docs/develop/theory/**' 2>/dev/null | head -20)
  if [ -n "$found" ]; then
    printf '%s\n' "$found"
    hits=$((hits + 1))
  else
    printf '(none)\n'
  fi

  if command -v gh >/dev/null 2>&1; then
    printf -- '--- open pull requests ---\n'
    prs=$(gh pr list --repo "$REPO" --state open --search "$term" \
            --limit 10 --json number,title \
            -q '.[]|"#\(.number) \(.title)"' 2>/dev/null || true)
    if [ -n "$prs" ]; then
      printf '%s\n' "$prs"
      hits=$((hits + 1))
    else
      printf '(none)\n'
    fi
  else
    printf -- '--- open pull requests: SKIPPED, gh not found ---\n'
  fi

  printf -- '--- remote branches ---\n'
  brs=$(git branch -r --list 'origin/*' 2>/dev/null \
          | grep -i -- "$term" | head -10 || true)
  if [ -n "$brs" ]; then
    printf '%s\n' "$brs"
    hits=$((hits + 1))
  else
    printf '(none)\n'
  fi
done

printf '\n'
if [ "$hits" -gt 0 ]; then
  printf 'PRIOR_ART_RESULT outcome=hits surfaces=%d\n' "$hits"
  printf 'Read them before dispatching. A seat that rediscovers an existing module\n'
  printf 'costs a full seat lifetime and produces a bind-only duplicate.\n'
  exit 3
fi
printf 'PRIOR_ART_RESULT outcome=clear\n'
exit 0
