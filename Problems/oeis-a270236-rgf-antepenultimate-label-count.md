---
slug: oeis-a270236-rgf-antepenultimate-label-count
bibkey: mathar2016a270236
doi: null
url: https://oeis.org/A270236
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/RestrictedGrowthLabelOccurrences
---

# The antepenultimate-label count in OEIS A270236

## Problem

OEIS A270236, NAME (verbatim):

> Triangle T(n,p) read by rows: the number of occurrences of p in the restricted growth functions of length n.

COMMENT defining the restricted growth functions (verbatim):

> The RG functions used here are defined by f(1)=1, f(j) <= 1+max_{i<j} f(i).

FORMULA (verbatim; R. J. Mathar, Mar 13 2016):

> Conjecture: T(n+1,n-1) = 2+n*(n+1)*(3*n^2-5*n+26)/24 for n>1.

Revision #22 records that Alois P. Heinz corrected the left index from
`T(n,n-2)` to the current `T(n+1,n-1)` on Mar 18 2016.

## Motivation

This is one of two independent formulas recorded as conjectures in the same
OEIS entry. The target is the complete unbounded identity for every natural
number `n > 1`, including the corrected left index and the entry's exact
natural-number quotient.

## Gap

The preregistration records a dated search on 2026-09-13: all 43 OEIS
revisions, arXiv API query `all:A270236` (0 hits), MathOverflow API (0 hits),
GitHub repository search (0 hits), pinned Mathlib, and 17 OEIS reverse
references were checked. Exact searches on Crossref, Semantic Scholar, and
Google Scholar also returned 0 hits. GitHub code search returned HTTP 401 and
OpenAlex returned HTTP 429, so those two surfaces were not verified. A proof
was not found in the checked surfaces; this is not an exhaustive
nonexistence or priority claim.

## Route

For the deficit parameter `k`, `card_two_repeat_words k` counts the
two-repeat layer as `C(k+2,3) + 3*C(k+2,4)`; in the source index this becomes
`C(n,3) + 3*C(n,4)`. The weighted label-extension identity
`secondLabelFiber` separates the top, one-repeat, and two-repeat maximum
layers and yields a recurrence for `T(n+1,n-1)`. Substituting `mathar_f1`,
using the choose recurrences, and normalizing the numerator by 24 gives
`2 + n*(n+1)*(3*n^2-5*n+26)/24`.

## Falsifier

A natural number `n > 1` for which the sum of occurrences differs from
`2 + n*(n+1)*(3*n^2-5*n+26)/24` would refute the assertion. A mismatch
between the recursive word model and the quoted restricted-growth condition,
or a failure to preserve the corrected index, would invalidate the claimed
identification with OEIS A270236.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/RestrictedGrowthLabelOccurrences.lean`.
- Main theorem: `mathar_f2`.
- Companion theorem: `mathar_f1` proves the entry's first conjecture and is
  used in the second proof.
- The canonical Lean report gives the std3 axioms `propext`,
  `Classical.choice`, and `Quot.sound` for both theorems.
- Full restricted-growth enumeration by the orchestrator checked F1 through
  `n = 9` with values `3, 5, 8, 12, 17, 23, 30, 38`, and F2 through `n = 8`
  with values `9, 21, 47, 97, 184, 324, 536`.
- The proof probe independently checked F1 through `n = 10` and F2 through
  `n = 9`; the search seat's block-deficit classification had no mismatch
  through `n = 10000`. These finite checks support but do not replace the
  universal Lean proofs.

## Triage

`theorem`. The formal theorem proves the full corrected
antepenultimate-label formula for every natural `n > 1`.

## ASSUMED-UNVERIFIED

The OEIS quotations, revision dates, literature-search readings, and finite
enumeration readings are supplied by issue #7365 and were not independently
repeated in this stage. Source-to-Lean identification is not itself a
kernel-checked fact, and no exhaustive literature or priority claim follows.
