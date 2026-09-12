#!/usr/bin/env bash
# External OEIS prior-art probe: has anyone outside this repository already
# formalised this A-number?
#
# Companion to prior-art.sh, which answers the other half of Rule 11 ("does this
# repository already have it"). The whole design problem here is that a miss must
# not read as novelty. Every corpus is queried by a method whose blind spots are
# known, every blind spot is printed, and **no output of this script ever asserts
# that a sequence has not been formalised** — the strongest thing it says is that
# the indexed paths it can see contain no match.
#
# Usage:
#   tools/scripts/agent/oeis-prior-art.sh A397349 [A000045 ...]
#
# Corpora and the shape each one has (measured 2026-09-13, trees untruncated):
#
#   provables/sequencelib   Lean 4 definitions of OEIS sequences, 26,336 paths.
#       25,465 distinct A-numbers appear in path names: 25,457 under
#       Sequencelib/Synthetic/<prefix>/, 49 under Sequencelib/AISynth/, 1 at the
#       top level. Those per-directory counts sum to 25,507, not 25,465, because
#       42 A-numbers appear in more than one directory. The Synthetic and AISynth
#       files are machine-written DEFINITIONS, not proofs. Observed range
#       A000004..A351831, nothing at or above A390000. Blind spot: 29 further
#       modules are named by concept (Fibonacci.lean, Catalan.lean, ...) and
#       carry their A-numbers only in file contents, which a path query cannot
#       see.
#
#   google-deepmind/formal-conjectures   1,733 paths, of which 227 are
#       FormalConjectures/OEIS/<decimal>.lean, the decimal being the A-number
#       with the 'A' and leading zeros stripped (A000040 -> 40.lean, verified by
#       reading that file). These are open `sorry` statements: a hit means the
#       conjecture is written down, not that it is settled.
#
#   plby/lean-proofs   46,436 paths, organised by arXiv identifier. ZERO
#       A-numbers occur in any path, so the file tree cannot answer this question
#       at all and this corpus is always reported UNKNOWN. Answering it needs a
#       content search of a clone, which this probe does not do.
#
# Exit codes:
#   0  no matching indexed path in any corpus that can answer
#   3  at least one hit; READ IT before dispatching
#   2  bad usage, missing dependency, or any query/transformation failure
#
# Failure is never reported as absence. Every step that could fail is checked,
# and a failed step exits 2 rather than producing a quiet miss.

set -uo pipefail

die() { printf 'oeis-prior-art: %s\n' "$1" >&2; exit 2; }

# --- validate every argument BEFORE touching the network -------------------
[ "$#" -ge 1 ] || die "usage: oeis-prior-art.sh <A-number> [<A-number> ...]"
command -v gh >/dev/null 2>&1 || die "gh not found"
command -v jq >/dev/null 2>&1 || die "jq not found"

ANUMS=()
for raw in "$@"; do
  anum=$(printf '%s' "$raw" | tr '[:lower:]' '[:upper:]') \
    || die "could not normalise argument: $raw"
  case "$anum" in
    A[0-9][0-9][0-9][0-9][0-9][0-9]) ANUMS+=("$anum") ;;
    *) die "not an A-number: $raw (expected A followed by exactly six digits)" ;;
  esac
done

CACHE_DIR="${OEIS_PRIOR_ART_CACHE:-${TMPDIR:-/tmp}/oeis-prior-art}"
CACHE_TTL_MIN="${OEIS_PRIOR_ART_TTL_MIN:-720}"
case "$CACHE_TTL_MIN" in
  ''|*[!0-9]*) die "OEIS_PRIOR_ART_TTL_MIN must be a whole number of minutes, got: $CACHE_TTL_MIN" ;;
esac
mkdir -p "$CACHE_DIR" || die "cannot create cache dir $CACHE_DIR"

SEQUENCELIB_REPO="${OEIS_SEQUENCELIB_REPO:-provables/sequencelib}"
FORMALCONJ_REPO="${OEIS_FORMALCONJ_REPO:-google-deepmind/formal-conjectures}"
LEANPROOFS_REPO="${OEIS_LEANPROOFS_REPO:-plby/lean-proofs}"

# grep that distinguishes "no match" (1) from "grep failed" (>1). A read error
# must never be indistinguishable from an absence.
grep_checked() {
  local out status
  out=$(grep -E "$1" "$2"); status=$?
  case "$status" in
    0) printf '%s' "$out"; return 0 ;;
    1) return 1 ;;
    *) die "grep failed with status $status on $2 (pattern: $1)" ;;
  esac
}

count_checked() {
  local out status
  out=$(grep -cE "$1" "$2"); status=$?
  case "$status" in
    0|1) printf '%s' "${out:-0}"; return 0 ;;
    *) die "grep -c failed with status $status on $2" ;;
  esac
}

# A cached tree is only trusted if it was published atomically after a validated
# fetch. A partial file left behind by a failed extraction would otherwise be
# read on the next run as a corpus that simply contains nothing.
fetch_tree() {
  local repo="$1" min_paths="$2" slug branch out tmp json fresh
  slug=$(printf '%s' "$repo" | tr '/' '_')
  out="$CACHE_DIR/$slug.paths"

  if [ -f "$out" ] && [ -s "$out" ]; then
    fresh=$(find "$out" -mmin "-$CACHE_TTL_MIN" 2>/dev/null) || fresh=""
    if [ -n "$fresh" ]; then
      local have; have=$(wc -l < "$out" 2>/dev/null) || have=0
      if [ "${have:-0}" -ge "$min_paths" ]; then printf '%s' "$out"; return 0; fi
      printf 'oeis-prior-art: cached tree for %s holds %s paths, fewer than the %s expected; refetching\n' \
        "$repo" "$have" "$min_paths" >&2
    fi
  fi

  branch=$(gh repo view "$repo" --json defaultBranchRef -q .defaultBranchRef.name 2>/dev/null) \
    || { printf 'oeis-prior-art: cannot resolve %s\n' "$repo" >&2; return 1; }
  [ -n "$branch" ] || { printf 'oeis-prior-art: empty default branch for %s\n' "$repo" >&2; return 1; }

  json=$(gh api "repos/$repo/git/trees/$branch?recursive=1" 2>/dev/null) \
    || { printf 'oeis-prior-art: tree query failed for %s\n' "$repo" >&2; return 1; }

  if [ "$(printf '%s' "$json" | jq -r '.truncated' 2>/dev/null)" != "false" ]; then
    printf 'oeis-prior-art: %s tree is TRUNCATED or unreadable; a miss would be a false negative\n' "$repo" >&2
    return 1
  fi

  tmp=$(mktemp "$CACHE_DIR/.$slug.XXXXXX") || return 1
  if ! printf '%s' "$json" | jq -r '.tree[].path' > "$tmp"; then
    rm -f "$tmp"; printf 'oeis-prior-art: could not extract paths for %s\n' "$repo" >&2; return 1
  fi
  local got; got=$(wc -l < "$tmp" 2>/dev/null) || got=0
  if [ "${got:-0}" -lt "$min_paths" ]; then
    rm -f "$tmp"
    printf 'oeis-prior-art: %s yielded %s paths, fewer than the %s expected; refusing to cache\n' \
      "$repo" "$got" "$min_paths" >&2
    return 1
  fi
  mv -f "$tmp" "$out" || { rm -f "$tmp"; return 1; }   # publish only after validation
  printf '%s' "$out"
}

sl_paths=$(fetch_tree "$SEQUENCELIB_REPO" 20000) || die "sequencelib tree unavailable"
fc_paths=$(fetch_tree "$FORMALCONJ_REPO" 1000)   || die "formal-conjectures tree unavailable"

sl_max=$(grep -oE 'A[0-9]{6}' "$sl_paths" | sort -u | tail -1) \
  || die "could not scan $SEQUENCELIB_REPO paths for A-numbers"
[ -n "$sl_max" ] || die "no A-number found in $SEQUENCELIB_REPO paths; the corpus or its layout changed"
sl_named=$(count_checked '^Sequencelib/[A-Z][A-Za-z]+\.lean$' "$sl_paths")
fc_total=$(count_checked '^FormalConjectures/OEIS/[0-9]+\.lean$' "$fc_paths")

hits=0
above_range=0

for anum in "${ANUMS[@]}"; do
  bare=${anum#A}
  bare=$(printf '%s' "$bare" | sed 's/^0*//') || die "could not normalise $anum"
  case "$bare" in
    '') bare=0 ;;
    *[!0-9]*) die "internal: bare form of $anum is not numeric: $bare" ;;
  esac

  printf '\n=== %s ===\n' "$anum"

  printf -- '--- %s ---\n' "$SEQUENCELIB_REPO"
  if sl_hit=$(grep_checked "(^|/)${anum}\.lean$" "$sl_paths"); then
    while IFS= read -r p; do
      case "$p" in
        Sequencelib/Synthetic/*) printf 'HIT  %s  [machine-synthesised DEFINITION, not a proof]\n' "$p" ;;
        Sequencelib/AISynth/*)   printf 'HIT  %s  [AI-synthesised DEFINITION, not a proof]\n' "$p" ;;
        *)                       printf 'HIT  %s  [curated definition]\n' "$p" ;;
      esac
    done <<< "$sl_hit"
    hits=$((hits + 1))
  elif [ "$anum" \> "$sl_max" ]; then
    printf 'NO SIGNAL  above this corpus range (highest indexed %s); a miss here means nothing\n' "$sl_max"
    above_range=$((above_range + 1))
  else
    printf 'no indexed path  (range A000004..%s; %s concept-named modules such as\n' "$sl_max" "$sl_named"
    printf '                 Fibonacci.lean carry A-numbers only in contents and are not searched)\n'
  fi

  printf -- '--- %s ---\n' "$FORMALCONJ_REPO"
  if fc_hit=$(grep_checked "^FormalConjectures/OEIS/${bare}\.lean$" "$fc_paths"); then
    printf 'HIT  %s  [open `sorry` statement: written down, not settled]\n' "$fc_hit"
    hits=$((hits + 1))
  else
    printf 'no indexed path  (%s OEIS statements indexed)\n' "$fc_total"
  fi

  printf -- '--- %s ---\n' "$LEANPROOFS_REPO"
  printf 'UNKNOWN  no A-number appears in any path of this repository; its file tree\n'
  printf '         cannot answer the question. Not evidence of absence.\n'
done

printf '\n'
if [ "$hits" -gt 0 ]; then
  printf 'RESULT hits=%d -- read them before dispatching\n' "$hits"
  exit 3
fi
printf 'RESULT no matching indexed path in any corpus searched.\n'
printf '       This does NOT establish absence and does NOT establish novelty:\n'
printf '       %s is not searchable by path at all (UNKNOWN);\n' "$LEANPROOFS_REPO"
printf '       %s concept-named sequencelib modules are not searched;\n' "$sl_named"
[ "$above_range" -gt 0 ] && \
  printf '       %d of the queries sit above the sequencelib range entirely (NO SIGNAL).\n' "$above_range"
printf '       Literature outside these three repositories is not consulted here.\n'
exit 0
