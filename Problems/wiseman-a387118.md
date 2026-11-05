---
slug: wiseman-a387118
bibkey: oeis2025wisemanpartitions
doi: null
url: https://oeis.org/A387118
triage: theorem
motivation_gids:
  - D5/S1/Words/Compositions/WisemanA387118
---

# Wiseman A387118 total partition identity

## Problem

OEIS A387118 asks whether the number of integer partitions of $n$ without choosable initial intervals equals the number of non-superdiagonal reversed integer partitions. The conjecture is preregistered in [#18602](https://github.com/the-omega-institute/trureturing/issues/18602).

### Statement echo

The formal count `a n` ranges over `Nat.Partition n` and filters the descending sort by the negation of `ChoosableInitial`. The comparison count `nonSuperdiagonal n` filters the ascending sort by the negation of `Superdiagonal`. The source predicates and sorting convention are imported from `D5/S1/Words/Compositions/ChoosableInitialIntervals`.

## Motivation

This is an externally stated OEIS conjecture. The delivered result is `D5/S1/Words/Compositions/WisemanA387118.result`, with admission basis `open-problem-resolution (#18602; Proved)`.

## Gap

The imported pointwise equivalence identifies the two predicates on every multiset. Applying negation and taking cardinalities over the same finite set of partitions supplies the total identity.

## Route

For every partition, `WisemanA388712.sorted_choosable_iff_superdiagonal` gives the equivalence between choosability of the descending parts and superdiagonality of the ascending parts. Negation preserves the equivalence, so the two filters defining `a` and `nonSuperdiagonal` are equal pointwise. `WisemanA387118.result` applies finite-cardinality congruence.

## Falsifier

A multiset whose two sorted predicates disagree, or a natural number with unequal filtered cardinalities, would refute the statement. The theorem has no finite cutoff.

## Evidence

The public result is kernel-checked in `D5/S1/Words/Compositions/WisemanA387118.lean` and mirrored by its Scribe. Its proof uses the imported `WisemanA388712.sorted_choosable_iff_superdiagonal` helper. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}.

The four-slot escape audit remains unfinished for the public result; [#22068](https://github.com/the-omega-institute/trureturing/issues/22068) records the missing typed infinite-family registration evidence. No `declared_validated` registration is claimed.

The finite comparison uses [the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/29dcaf8a7cfd8f069c88eff27acd8735cfdfc4d1/docs/reports/oeis-a388712-a387118-a388713-choosable-initial-intervals). The command `python3 /Users/auric/trureturing-experiments/docs/reports/oeis-a388712-a387118-a388713-choosable-initial-intervals/check.py 22` exits $0$; `check.py` has SHA-256 `2d3874df9fddbc803aa9b2465993e883039fff3da1b51691245f6297ffa335c1`. It exhausts positive partitions for $1 \le n \le 22$. The published-prefix comparison for this entry has scope $n \le 22$.

## Triage

1. **Proved, kernel-checked:** the equality `a n = nonSuperdiagonal n` for every natural number, by `D5/S1/Words/Compositions/WisemanA387118.result`.
2. **Proved, kernel-checked:** the shared pointwise predicate equivalence, supplied by `D5/S1/Words/Compositions/WisemanA388712.sorted_choosable_iff_superdiagonal`.
3. **Computed:** the pinned experiment exhausts positive partitions through $n=22$ and compares the published A387118 values at that scope; `python3 check.py 22` exits 0 with script SHA-256 `2d3874df9fddbc803aa9b2465993e883039fff3da1b51691245f6297ffa335c1`.
4. **Open:** literature completeness and publication priority beyond the recorded search scope.

## ASSUMED-UNVERIFIED

The finite computation has only the stated range. The literature screen is bounded and does not establish a priority claim. The escape audit is unfinished at #22068.
