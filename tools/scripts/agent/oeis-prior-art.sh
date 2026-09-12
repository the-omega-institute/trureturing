#!/usr/bin/env bash
# External OEIS prior-art probe: has anyone outside this repository already
# formalised this A-number?
#
# Companion to prior-art.sh, which answers the other half of Rule 11 ("does this
# repository already have it"). The whole design problem here is that a miss must
# not read as novelty, so each corpus is queried by a method whose blind spots
# are known and the report states them. A corpus that cannot answer says UNKNOWN;
# it never says "absent".
#
# Usage:
#   tools/scripts/agent/oeis-prior-art.sh A397349 [A000045 ...]
#
# Corpora and the shape each one actually has (measured 2026-09-13):
#
#   provables/sequencelib   Lean 4 definitions of OEIS sequences. 25,465
#       A-numbers reachable from file paths, of which 25,457 sit under
#       Sequencelib/Synthetic/<prefix>/ and 49 under Sequencelib/AISynth/ --
#       machine-written DEFINITIONS, not proofs. A hit says the sequence has
#       been defined; it never says anything about it has been proved. Observed
#       range A000004..A351831 with nothing at or above A390000, so a miss up
#       there carries no signal and is reported as such. Known blind spot: 29
#       further modules are named by concept (Fibonacci.lean, Catalan.lean, ...)
#       and carry their A-numbers only in file contents, so a path query cannot
#       see them; "absent" below means "absent from the A-number-named files".
#
#   google-deepmind/formal-conjectures   227 files under FormalConjectures/OEIS/,
#       named by the A-number with the 'A' and leading zeros stripped
#       (A000045 -> 45.lean). These are open `sorry` statements: a hit means the
#       conjecture is already written down, not that it is settled.
#
#   plby/lean-proofs   46,436 Lean files organised by arXiv identifier; ZERO
#       A-numbers occur in any path. The file tree carries no signal at all for
#       this question, so this corpus is always reported UNKNOWN. Answering it
#       needs a content search of a clone, which this probe deliberately does
#       not do.
#
# Exit codes:
#   0  no hit in any corpus that can answer (corpora that cannot said UNKNOWN)
#   3  at least one hit; READ IT before dispatching
#   2  bad usage, missing dependency, or a corpus query failed

set -uo pipefail

die() { printf 'oeis-prior-art: %s\n' "$1" >&2; exit 2; }

[ "$#" -ge 1 ] || die "usage: oeis-prior-art.sh <A-number> [<A-number> ...]"
command -v gh >/dev/null 2>&1 || die "gh not found"
command -v jq >/dev/null 2>&1 || die "jq not found"

CACHE_DIR="${OEIS_PRIOR_ART_CACHE:-${TMPDIR:-/tmp}/oeis-prior-art}"
CACHE_TTL_MIN="${OEIS_PRIOR_ART_TTL_MIN:-720}"
mkdir -p "$CACHE_DIR" || die "cannot create cache dir $CACHE_DIR"

SEQUENCELIB_REPO="${OEIS_SEQUENCELIB_REPO:-provables/sequencelib}"
FORMALCONJ_REPO="${OEIS_FORMALCONJ_REPO:-google-deepmind/formal-conjectures}"
LEANPROOFS_REPO="${OEIS_LEANPROOFS_REPO:-plby/lean-proofs}"

# Fetch a repository's full recursive file tree into the cache.
# Fails closed when GitHub truncates the response: a truncated tree would turn
# every miss into a false negative, which is the one failure this probe exists
# to prevent.
fetch_tree() {
  local repo="$1" slug branch out age
  slug=$(printf '%s' "$repo" | tr '/' '_')
  out="$CACHE_DIR/$slug.paths"

  if [ -f "$out" ]; then
    age=$(find "$out" -mmin "+$CACHE_TTL_MIN" 2>/dev/null | wc -l)
    [ "$age" -eq 0 ] && { printf '%s' "$out"; return 0; }
  fi

  branch=$(gh repo view "$repo" --json defaultBranchRef -q .defaultBranchRef.name 2>/dev/null) \
    || { printf 'oeis-prior-art: cannot resolve %s\n' "$repo" >&2; return 1; }
  [ -n "$branch" ] || { printf 'oeis-prior-art: empty default branch for %s\n' "$repo" >&2; return 1; }

  local json
  json=$(gh api "repos/$repo/git/trees/$branch?recursive=1" 2>/dev/null) \
    || { printf 'oeis-prior-art: tree query failed for %s\n' "$repo" >&2; return 1; }

  if [ "$(printf '%s' "$json" | jq -r '.truncated')" != "false" ]; then
    printf 'oeis-prior-art: %s tree is TRUNCATED; a miss would be a false negative\n' "$repo" >&2
    return 1
  fi

  printf '%s' "$json" | jq -r '.tree[].path' > "$out" || return 1
  printf '%s' "$out"
}

sl_paths=$(fetch_tree "$SEQUENCELIB_REPO") || die "sequencelib tree unavailable"
fc_paths=$(fetch_tree "$FORMALCONJ_REPO") || die "formal-conjectures tree unavailable"

sl_max=$(grep -oE 'A[0-9]{6}' "$sl_paths" | sort -u | tail -1)
sl_named=$(grep -cE '^Sequencelib/[A-Z][A-Za-z]+\.lean$' "$sl_paths")

hits=0

for raw in "$@"; do
  anum=$(printf '%s' "$raw" | tr '[:lower:]' '[:upper:]')
  case "$anum" in
    A[0-9][0-9][0-9][0-9][0-9][0-9]) : ;;
    *) die "not an A-number: $raw (expected A followed by six digits)" ;;
  esac
  bare=$(printf '%s' "${anum#A}" | sed 's/^0*//')
  [ -n "$bare" ] || bare=0

  printf '\n=== %s ===\n' "$anum"

  # --- provables/sequencelib -------------------------------------------------
  printf -- '--- %s ---\n' "$SEQUENCELIB_REPO"
  sl_hit=$(grep -E "(^|/)${anum}\.lean$" "$sl_paths" || true)
  if [ -n "$sl_hit" ]; then
    printf '%s\n' "$sl_hit" | while IFS= read -r p; do
      case "$p" in
        Sequencelib/Synthetic/*) printf 'HIT  %s  [machine-synthesised DEFINITION, not a proof]\n' "$p" ;;
        Sequencelib/AISynth/*)   printf 'HIT  %s  [AI-synthesised DEFINITION, not a proof]\n' "$p" ;;
        *)                       printf 'HIT  %s  [curated definition]\n' "$p" ;;
      esac
    done
    hits=$((hits + 1))
  elif [ "$anum" \> "$sl_max" ]; then
    printf 'NO SIGNAL  above this corpus range (max observed %s); a miss here means nothing\n' "$sl_max"
  else
    printf 'absent from A-number-named files  (range A000004..%s; %d concept-named\n' \
      "$sl_max" "$sl_named"
    printf '        modules such as Fibonacci.lean carry A-numbers only in contents)\n'
  fi

  # --- google-deepmind/formal-conjectures ------------------------------------
  printf -- '--- %s ---\n' "$FORMALCONJ_REPO"
  fc_hit=$(grep -E "^FormalConjectures/OEIS/${bare}\.lean$" "$fc_paths" || true)
  if [ -n "$fc_hit" ]; then
    printf 'HIT  %s  [open `sorry` statement: written down, not settled]\n' "$fc_hit"
    hits=$((hits + 1))
  else
    printf 'absent  (%s OEIS statements indexed)\n' \
      "$(grep -cE '^FormalConjectures/OEIS/[0-9]+\.lean$' "$fc_paths")"
  fi

  # --- plby/lean-proofs ------------------------------------------------------
  printf -- '--- %s ---\n' "$LEANPROOFS_REPO"
  printf 'UNKNOWN  no A-number appears in any path of this repository; the file\n'
  printf '         tree cannot answer the question. Not evidence of absence.\n'
done

printf '\n'
if [ "$hits" -gt 0 ]; then
  printf 'RESULT hits=%d -- read them before dispatching\n' "$hits"
  exit 3
fi
printf 'RESULT hits=0 -- no answering corpus has it; %s remains UNKNOWN\n' "$LEANPROOFS_REPO"
exit 0
