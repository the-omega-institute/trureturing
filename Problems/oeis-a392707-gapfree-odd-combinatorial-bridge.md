---
slug: oeis-a392707-gapfree-odd-combinatorial-bridge
bibkey: oeis2026a392707
doi: null
url: https://oeis.org/A392707
triage: theorem
motivation_gids:
  - D5/S1/Words/Compositions/ZeroPrependedFirstSumsOddParts
---

# Strict First Sums and Gapfree Odd Partitions

## Problem

OEIS A392707, revision 10, states:

> Conjecture: Reversed integer partitions of this type (with strictly increasing 0-based partial alternating sums) are counted by A053251.

The formal target here is the self-contained combinatorial bridge: for every
n, the number of partitions with a strictly increasing positive preimage s
under firstSums(0::s) equals the number of partitions whose support is exactly
{1,3,...,2k-1} for some k. The two classes include the empty partition.
The further equality with mock theta coefficients is not formalized here.

## Motivation

This is a first-tier 2026 OEIS comment conjecture. The caller derived the
increment parametrization and checked n=1,...,15; those were not kernel
proofs. The weak version has just landed in PR #6600, and is the direct
formal prerequisite. This module imports and reuses its actual equivalence,
sum proof, injectivity and list/partition interfaces.

## Gap

The weak cardinal theorem alone does not identify the images of strict
preimages. Its direct application and normalization fail the bind-only probe.
The missing formal fact is that strictly decreasing positive Young-diagram
row lengths are equivalent to column heights containing every integer from
1 to the maximum. That fact restricts the frozen bijection to the new classes.

All 53 A-numbers in the two roots' comment/formula/xref fields were retrieved
in full (54 entries including the roots). A053251 already states the gapfree
odd interpretation and the psi expansion. A392694 and A392703 still repeat
the strict-count claim conjecturally. The inspected Gordon/Connor citations
concern different alternately strict partition statements. No published proof
of this first-sums bridge was located in the examined entries; no exhaustive
absence claim is made.

## Route

Use the existing firstSums definition and the existing weak correspondence.
For strict s, each increment ti=si-s(i-1) is positive, including t1=s1.
The sibling's conjugation followed by h -> 2h-1 sends those increments to
the multiplicities of 2k-1,2k-3,...,1. The new proof identifies a column of
height h with a strict drop between row h-1 and row h, proves both support
directions, and uses the maximum height to fix the interval endpoint.
It then restricts the original weight-preserving equivalence to these
predicates and to sum n. No weight identity or inverse is reproved.

A053251's formula is psi(q)=sum(k>=1) q^(k*k)/prod(i=1..k)(1-q^(2i-1)).
For n>=1 its stated combinatorial interpretation is the endpoint above.
At n=0 A053251 is 0, whereas both formal classes have count 1. Thus the
empty-inclusive generating series is 1+psi(q); this series assertion is
documentary, not a theorem of this Lean module.

## Falsifier

A strict preimage whose image misses a smaller odd part, a gapfree odd
partition whose inverse has a repeated row, a weight discrepancy, or any n
with unequal counts would refute the combinatorial bridge. A subset-only
or superset-only support condition would state a different theorem.

## Evidence

The public theorem is `card_strictFirstSums_eq_gapfreeOdd` in
`D5/S1/Words/Compositions/StrictFirstSumsGapfreeOddParts.lean`. The complete
file has passed the warm-tree Lean compiler without diagnostics. Full gate
receipts and frozen identity are recorded in the Library note and attempt.

The worker independently enumerated every partition for n=0,...,15, using
integer subtraction for the inverse recurrence. The caller supplied the
same positive-index counts. Actual worker readings:

| n | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Qualifying | 1 | 1 | 1 | 1 | 2 | 2 | 2 | 3 | 3 | 4 | 5 | 5 | 6 | 7 | 8 | 9 |
| Gapfree odd | 1 | 1 | 1 | 1 | 2 | 2 | 2 | 3 | 3 | 4 | 5 | 5 | 6 | 7 | 8 | 9 |
| A053251 | 0 | 1 | 1 | 1 | 2 | 2 | 2 | 3 | 3 | 4 | 5 | 5 | 6 | 7 | 8 | 9 |

All 60 qualifying instances have no weight violations or duplicate images,
and their exact image sets equal the gapfree odd partition sets.
Nonempty witness: y=[1,3,6], s=[1,2,4], t=[1,1,2], odd image=[1,1,3,5],
both sums 10. Gapped witness: odd parts [1,5], missing 3, total 6; the weak
inverse is s=[1,1,2], producing y=[1,2,3], which fails strictness.
The empty lists give actual counts 1 and 1; length-one s=[a] maps to a
copies of 1 for every positive a, with source y=[a] and equal weight a.

## Triage

`theorem` for the combinatorial bridge, with admission basis escape-witness.
The full OEIS/mock-theta identification is not claimed as a formal resolution,
so the Scribe document carries no OpenProblemResolutionClaim for it.
The sibling's helpers are private; the local elaborator returns their unique
existing constants from the imported environment, without copying them.
That explicit dependency on the frozen private interface is a limitation.

## ASSUMED-UNVERIFIED

The caller's derivation and n<=15 checks were not kernel proofs. The caller
initially marked the psi expansion ASSUMED-UNVERIFIED; this worker verified
it is written on A053251, but did not formalize its series identity.
No exhaustive literature search, priority, mathematical novelty, independent
review, multi-model consensus, or implication to any larger conjecture is
claimed. Unopened linked papers remain ASSUMED-UNVERIFIED. Source fidelity
is documentary; Lean checks the explicit predicates and unbounded count.
