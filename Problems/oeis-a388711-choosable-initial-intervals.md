---
slug: oeis-a388711-choosable-initial-intervals
bibkey: oeis2026a388711
doi: null
url: https://oeis.org/A388711
triage: theorem
motivation_gids:
  - D5/S1/Words/Compositions/ChoosableInitialIntervals
---

# Choosable Initial Intervals and Reversed Partitions

## Problem

OEIS A388711 counts partitions of n into k positive parts whose initial
intervals admit distinct representatives. Its comment conjectures that the
same number counts superdiagonal reversed partitions: the parts in increasing
order satisfy y_i >= i at every one-based position.

## Motivation

This is a first-tier recent OEIS comment conjecture. The implementation brief
calls it a 2026 conjecture; direct access to the OEIS JSON on September 9,
2026 instead gives author date September 23, 2025 and creation date September
25, 2025. The requested bibliographic key is retained. The definition and
conjecture wording agree exactly with the brief.

## Gap

The initial-interval SDR criterion is elementary and may be folklore. General
Hall theory is classical; no novelty of that criterion is claimed. In the
searched pinned Mathlib and public Lean indexes, no target characterization
was found. Direct Hall instantiation leaves subfamily-union cardinal bounds,
so it does not finish the stated equivalence by normalization alone.

## Route

For a weakly increasing list, restrict a representative map to its first i+1
positions. Every chosen positive integer is at most the part at position i.
Subtracting one yields an injection from Fin(i+1) into Fin(y_i), hence
i+1 <= y_i by Mathlib's finite cardinal comparison. Conversely, the choice
f(i)=i+1 witnesses choosability whenever the superdiagonal inequalities hold.

Order invariance transports a nodup list of representatives through a
permutation using Mathlib's relational permutation lemma. Thus the same
finite type Nat.Partition(n), restricted to exactly k parts, can be filtered
by choosability of its descending parts or by superdiagonality of its
ascending reversed parts. The filters, and therefore their cardinalities,
are equal. No Hall theorem is imported by the implementation.

## Falsifier

An increasing list with distinct positive interval representatives but with
y_i < i+1, or a superdiagonal list with no such representatives, would
contradict the list equivalence. A mismatch of the two filters at any n,k
would contradict the counting identity. There is no finite cutoff.

## Evidence

The module is `D5/S1/Words/Compositions/ChoosableInitialIntervals.lean`.
The public results are `choosableInitial_iff_superdiagonal`,
`choosableInitial_congr_perm`, and `card_choosable_eq_superdiagonal`.
The live combinatorial witness is the private `prefix_capacity` construction.
The Library note contains the ordered search receipts, bind-only attempt,
per-declaration shape analysis, and validation checkpoints.

The caller reports exhaustive SDR backtracking and direct superdiagonal
checks for every cell with n=1,...,13, with zero mismatches and agreement with
OEIS after aligning its n=0 and k=0 entries. This is caller evidence, not a
claim that the worker reran that entire range.

The boundary obligations are [1,2,3] (both predicates true), [1,1,4] (both
false), [] (both true), and [0] (both false). The empty partition is the only
partition of zero; no positive n has a partition with zero parts. Therefore
the empty-list convention gives T(0,0)=1 and T(n,0)=0 for n>0.

## Triage

`theorem`: the exact unbounded list and partition-count statements are
implemented. Final kernel, frozen-state and PR validation is recorded in the
Library note and runner result; source priority is a separate question.

## ASSUMED-UNVERIFIED

No exhaustive literature search, absence of a proof anywhere in the
literature, first-publication priority, or implication to a larger conjecture
is claimed. The caller's four-group web search did not locate a published
statement of the partition identity. The underlying criterion may be a
familiar Hall consequence. Source-to-formal-definition correspondence is
documentary; the Lean kernel verifies the explicitly defined quantities.
The worker performs implementation and self-checks; independent review is
not claimed by this entry.
