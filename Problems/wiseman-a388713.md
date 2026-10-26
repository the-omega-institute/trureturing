---
slug: wiseman-a388713
bibkey: oeis2025wisemanpartitions
doi: null
url: https://oeis.org/A388713
triage: theorem
motivation_gids:
  - D5/S1/Words/Compositions/WisemanA388713
---

# Wiseman A388713 maximum-refined partition identity

## Problem

OEIS A388713 asks whether the number of superdiagonal reversed partitions of $n$ with maximum $k$ equals the number of integer partitions of $n$ with maximum $k$ and choosable initial intervals. The conjecture is preregistered in [#18603](https://github.com/the-omega-institute/trureturing/issues/18603).

### Statement echo

The formal count `T n k` filters `Nat.Partition n` by `p.parts.sup = k` and superdiagonality of the ascending sort. The comparison count `choosable n k` uses the same maximum condition and choosability of the descending sort. The source predicates and sorting convention are imported from `D5/S1/Words/Compositions/ChoosableInitialIntervals`.

## Motivation

This is an externally stated OEIS conjecture. The delivered result is `D5/S1/Words/Compositions/WisemanA388713.result`, with admission basis `open-problem-resolution (#18603; Proved)`.

## Gap

The imported pointwise equivalence identifies the two predicates on every multiset. Conjoining the common maximum condition and taking finite cardinalities supplies the maximum-refined identity.

## Route

For every partition, the reverse of `WisemanA388712.sorted_choosable_iff_superdiagonal` gives superdiagonality of the ascending parts exactly when the descending parts are choosable. The shared predicate `p.parts.sup = k` is preserved, so the two filters defining `T` and `choosable` are equal pointwise. `WisemanA388713.result` applies finite-cardinality congruence.

The empty partition has maximum zero and both formal counts are one at $(0,0)$; the printed source row uses zero there. The identity concerns the common formal convention.

## Falsifier

A multiset whose sorted predicates disagree, or a pair $(n,k)$ with unequal filtered cardinalities, would refute the statement. The theorem has no finite cutoff.

## Evidence

The public result is kernel-checked in `D5/S1/Words/Compositions/WisemanA388713.lean` and mirrored by its Scribe. Its proof uses the imported `WisemanA388712.sorted_choosable_iff_superdiagonal` helper. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}.

The four-slot escape audit remains unfinished for the public result; [#22068](https://github.com/the-omega-institute/trureturing/issues/22068) records the missing typed infinite-family registration evidence. No `declared_validated` registration is claimed.

## Triage

1. **Proved, kernel-checked:** the equality `T n k = choosable n k` for every pair of natural numbers, by `D5/S1/Words/Compositions/WisemanA388713.result`.
2. **Proved, kernel-checked:** the shared pointwise predicate equivalence, supplied by `D5/S1/Words/Compositions/WisemanA388712.sorted_choosable_iff_superdiagonal`.
3. **Computed:** the pinned experiment exhausts positive partitions through $n=22$ and compares the published A388713 prefix at that scope; `python3 check.py 22` exits 0 with script SHA-256 `2d3874df9fddbc803aa9b2465993e883039fff3da1b51691245f6297ffa335c1`.
4. **Open:** literature completeness and publication priority beyond the recorded search scope.

## ASSUMED-UNVERIFIED

The finite computation has only the stated range and uses the source row-zero convention for comparison. The literature screen is bounded and does not establish a priority claim. The escape audit is unfinished at #22068.
