---
bibkey: oeis2025wisemanpartitions
authors: Gus Wiseman
year: 2025
title: OEIS A388712, A387118 and A388713
doi: null
url: https://oeis.org/A388712
claim: The three conjectures equate choosable initial-interval partition counts and superdiagonal reversed-partition counts, with complementation or a common statistic.
strata_touched:
  - D5/S1/Words/Compositions/WisemanA388712
  - D5/S1/Words/Compositions/WisemanA387118
  - D5/S1/Words/Compositions/WisemanA388713
license: citation-only
triage: anchor
---

## Verified locator

Source: https://oeis.org/A388712

Related entries: https://oeis.org/A387118 and https://oeis.org/A388713.
These OEIS entries are unpaginated; the locators below specify their Name
and Comments fields. The source snapshot is `oeis/oeisdata` at `e7d0073e`.

# Wiseman's partition-count conjectures

## A388712

Name:

> Triangle read by rows where T(n,k) is the number of integer partitions of n into k parts without choosable initial intervals.

Comments:

> Conjecture: Also the number of non-superdiagonal reversed partitions of n into k parts, where a sequence (y_1, ..., y_k) is superdiagonal iff y_i >= i for all i = 1..k.

## A387118

Name:

> Number of integer partitions of n without choosable initial intervals.

Comments:

> Conjecture: Also the number of non-superdiagonal reversed integer partitions of n. - _Gus Wiseman_, Oct 04 2025

## A388713

Name:

> Triangle read by rows where T(n,k) is the number of superdiagonal multisets summing to n (reversed partitions of n) with maximum k.

Comments:

> Conjecture: Also the number of integer partitions of n with maximum k and choosable initial intervals.

A388712 also defines the objects as follows:

> We say that a set or sequence of nonempty sets is choosable iff it is possible to choose a different element from each set. … The initial interval of a nonnegative integer x is the set {1,...,x}.

A388713 states:

> A sequence (y_1, ..., y_k) is superdiagonal iff y_i >= i for all i = 1..k.

Ordinary parts are sorted decreasingly, reversed parts increasingly. The
existing ChoosableInitial and Superdiagonal predicates express distinct
positive representatives and the one-based bound. Nat.Partition has positive
parts. The first two identities count failures of these predicates, refined
by number of parts in A388712. A388713 counts successes with maximum
Multiset.sup. Its empty partition has maximum zero; both Lean counts are 1
at (0,0), whereas the source prints 0 in row 0. The common empty-partition
value does not affect the identity.

The proofs reuse permutation invariance and the increasing-list criterion
in D5/S1/Words/Compositions/ChoosableInitialIntervals. No claim of novelty
for that elementary consequence of the distinct-representative criterion
is made.

## Finite comparison

The experiment is
`docs/reports/oeis-a388712-a387118-a388713-choosable-initial-intervals/`
in https://github.com/the-omega-institute/trureturing-experiments,
commit `29dcaf8a7cfd8f069c88eff27acd8735cfdfc4d1`.
The checker `check.py` has sha256
`2d3874df9fddbc803aa9b2465993e883039fff3da1b51691245f6297ffa335c1`.
The source records `python3 check.py 22`, exit 0, ending in `RESULT PASS`.
It exhausts partitions through n=22 and compares all three data sets, using
the source's printed row-zero value for A388713. This finite comparison is
separate from the universal Lean identities.

## Literature boundary

The source screen on issues #18601, #18602 and #18603 checked the OEIS
entries, repository declarations and public Lean problem collections.
Related literature is P. Hall, *On Representatives of Subsets*, Journal of the London Mathematical Society 10 (1935), 26–30, DOI `10.1112/jlms/s1-10.37.26`; Peter J. Cameron, *Hall's marriage theorem*, [arXiv:2503.23159v1](https://arxiv.org/abs/2503.23159v1); and M. Archibald, A. Blecher, S. Elizalde and A. Knopfmacher, *Subdiagonal and superdiagonal partitions*, Afrika Matematika 36, article 77 (2025), DOI `10.1007/s13370-025-01282-0`. The first two state the distinct-representative criterion; they are not on these modules' Lean dependency paths. The third studies superdiagonal partition enumeration; it is not on these modules' dependency paths either. No prior settlement of the three named identities was found in the OEIS text, visible history and exact-name / choosability / superdiagonal searches over arXiv and web sources. This is a searched-scope statement, not a priority claim. Exhaustive literature
completeness and publication priority are ASSUMED-UNVERIFIED.
