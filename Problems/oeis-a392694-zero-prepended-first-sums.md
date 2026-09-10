---
slug: oeis-a392694-zero-prepended-first-sums
bibkey: oeis2026a392694
doi: null
url: https://oeis.org/A392694
triage: theorem
motivation_gids:
  - D5/S1/Words/Compositions/ZeroPrependedFirstSumsOddParts
---

# Zero-Prepended First Sums and Odd Parts

## Problem

OEIS A392694, revision 7 (January 25, 2026), states:

> Conjecture: Reversed integer partitions of this type (with weakly increasing 0-based partial alternating sums) are counted by A000009.

A reversed partition is a weakly increasing positive integer list y.
The alternating recurrence is s0=0, sj=yj-s(j-1), and the condition is that
0,s1,...,sk is weakly increasing. A000009(n) counts distinct-part partitions
of n. The claim has no shift.

## Motivation

This is a first-tier 2026 OEIS comment conjecture. The caller supplied the
odd-multiplicity reparametrization and checked every qualifying partition
through n=15. That derivation and computation were not a kernel proof.
A392698 instead uses decreasing partitions and pairwise distinct alternating
sums; it is a different target and is not imported or modified here.

## Gap

Pinned Mathlib already proves Euler's odd/distinct partition identity.
A direct application does not establish the source's first-sums predicate.
The bind-only probe leaves equality of different filtered cardinalities after
unfolding and Euler rewriting. The missing content is a weight-preserving
bijection from qualifying reversed partitions to odd-part partitions.

All 32 A-numbers in A392694's comment/formula/xref fields were retrieved as
complete JSON entries. No proof of this bridge was located in those entries.
A392707 calls it an "apparent count A000009", a conjectural restatement, not
a proof. Classical Euler proofs and the opened Arndt book have a different
scope. The Library note records each entry, revision, and finding.

## Route

Reuse `FirstSumsPartitionCharacterization.firstSums`, the existing adjacent
sums of a list. Define qualification by existence of an increasing positive
list s with firstSums(0::s)=y. This is the stated recurrence: yj=s(j-1)+sj.
For nonempty qualifying y, s1=y1>0, so monotonicity makes every sj positive.
Conversely an increasing positive s gives an increasing positive y.
The fixed zero start makes the preimage unique.

For k entries set t1=s1>=1 and ti=si-s(i-1)>=0. Then
sum(y)=sum_i ti*(2*(k-i)+1). Formally, reverse s into positive Young-diagram
row lengths, transpose, and map each column height h to 2*h-1. A height
k-i+1 occurs ti times. This is exactly the odd-multiplicity map; the positive
rows prevent nonexistent leading rows from giving extra representations.
Mathlib supplies transposition and its equivalence with row lengths. The
new proof establishes invertibility and preservation of total weight,
restricts to sum n, and uses multiset sorting to reach Nat.Partition n.
Finally apply `Nat.Partition.card_odds_eq_card_distincts`.

## Falsifier

A qualifying list whose odd image has a different weight, two qualifying
lists with the same odd image, or an odd partition without a qualifying
preimage would refute the bridge. Any n with unequal source and distinct-part
counts would refute the target. There is no upper bound on n in the theorem.

## Evidence

The module is `D5/S1/Words/Compositions/ZeroPrependedFirstSumsOddParts.lean`.
The public bridge is `card_zeroPrependedFirstSums_eq_odds`; the endpoint is
`card_zeroPrependedFirstSums_eq_distincts`. The complete module compiles with
no diagnostics. Full repository gate receipts and frozen identity are
recorded in the Library note and runner result as they become available.

Caller readings and independent worker enumeration both give:

| n | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Qualifying | 1 | 1 | 1 | 2 | 2 | 3 | 4 | 5 | 6 | 8 | 10 | 12 | 15 | 18 | 22 | 27 |
| Odd parts | 1 | 1 | 1 | 2 | 2 | 3 | 4 | 5 | 6 | 8 | 10 | 12 | 15 | 18 | 22 | 27 |
| Distinct parts | 1 | 1 | 1 | 2 | 2 | 3 | 4 | 5 | 6 | 8 | 10 | 12 | 15 | 18 | 22 | 27 |

The worker checked all 137 qualifying instances: zero weight violations,
zero duplicate images, and exact equality of the image set with the odd-part
set for every n in this range. Python uses integer subtraction for the
recurrence. These checks support definition fidelity; the unbounded proof
does not depend on numerical enumeration.

Nonempty witness: y=[2,4,4], s=[2,2,2], t=[2,0,0], odd image [5,5], total 10.
Euler's binary-multiplicity bijection gives the distinct partition [10].
Nonqualifying witness: y=[2,3] gives the unique s=[2,1]; the second monotonicity
comparison 2<=1 fails. At n=0 the empty partition qualifies and all three
counts were actually computed as 1; no zero part is allowed.

## Triage

`theorem`: the exact unbounded count has been implemented. The module's
admission basis is `escape-witness`; Euler's theorem is the existing endpoint.
The Library note separates source investigation, formal proof, finite checks,
and publication status.

## ASSUMED-UNVERIFIED

No exhaustive literature search, absence of a proof anywhere, mathematical
novelty, first-publication priority, or implication to a larger conjecture is
claimed. Linked pages not individually opened are ASSUMED-UNVERIFIED.
The caller's derivation was not a kernel proof and the caller did not conduct
the literature search. Source-to-definition fidelity remains documentary;
the kernel verifies the explicitly defined predicates and cardinalities.
This worker implemented and self-checked the proof; independent review or
multi-model consensus is not claimed here.
