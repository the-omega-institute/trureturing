---
bibkey: barcenapetisco2025fibonaccipartitions
authors: Jon Asier Bárcena-Petisco, Luis Martínez, María Merino, Juan Manuel Montoya, Antonio Vera-López
year: 2025
title: "Fibonacci-like partitions and their associated piecewise-defined permutations"
doi: null
url: https://arxiv.org/abs/2503.19696
claim: "Conjecture 6.3: for the non-negative integers q(i,j) produced by Algorithm 1, for every i >= 1 the sequence {q(i,j)}_j is a permutation of the non-negative integers, and for all i1 < i2 every integer appears exactly once in {q(i1,j) - q(i2,j)}_j."
strata_touched: []
license: citation-only
triage: anchor
---

# Bárcena-Petisco, Martínez, Merino, Montoya and Vera-López, greedy difference matrix

The paper states Conjecture 6.3 as its main open question and object of future research. It
proves the `i = 2` case as Theorem 5.1 and reports computational evidence for the first seven
rows. Nothing in this repository proves any of it. This note records what an attempt on the
next row established, so that a later attempt starts from the obstruction.

## The construction

    q(i,j) = 0                                                 if i = 0 or j = 0
    q(i,j) = mex ( { q(i,k) + q(l,j) - q(l,k) : 0 <= l < i, 0 <= k < j } ∩ ℤ≥0 )   otherwise

The construction is nested: `q(i,j)` does not depend on how far the matrix is extended. Row 1
is forced to be the identity, since `q(0,·) = 0` makes the excluded set `{q(1,k) : k < j}`.

## Row 2 is the Wythoff involution

This is the substantive finding and it is not stated in the paper, which says only that row 2
is a permutation. With `φ = (1+√5)/2`, `A(n) = ⌊nφ⌋` and `B(n) = A(n) + n` the lower and upper
Wythoff sequences,

    q(2, A(n)) = B(n)      and      q(2, B(n)) = A(n).

Verified for `n = 1..120` with no violation. Row 2 begins `0, 2, 1, 5, 7, 3, 10, 4, 13, 15, 6,
18, 20, 8`; `A` begins `1, 3, 4, 6, 8, 9, 11, 12, 14, 16` and `B` begins `2, 5, 7, 10, 13, 15,
18, 20, 23, 26`. So row 2 is the involution exchanging the two Wythoff sequences, which is what
the paper's title refers to and what connects this construction to Zeckendorf representations.

The paper states this identification itself, and the reconstruction above was avoidable. In the
paragraph following Proposition 5.6: "The sequence q_n corresponds with sequence A002251 in
Sloane's on-line encyclopedia of integer sequences, obtained by swapping a(k) and b(k) for all
k >= 1. This is evident from the expression for q_n given in Lemma 5.5." So row 2 is A002251 on
the authors' own account, not on ours; what the computation above adds is only an independent
check of their claim through index 120.

A002251 is defined as "start with the nonnegative integers; then swap L(k) and U(k) for all
k >= 1, where L = A000201, U = A001950 (lower and upper Wythoff sequences)". Querying OEIS with
the terms `0, 2, 1, 5, 7, 3, 10, 4, 13, 15, 6, 18, 20, 8` returns it directly, which is how the
same identification is reachable when a source does not supply it.

The same query on the first twenty terms of row 3 returns nothing. That is evidence that row 3
has not been catalogued; it is not evidence that row 3 has no description.

## Why row 3 does not follow by analogy

The extra translates available at `l = 2` break the involution. The smallest violation is at
`j = 4`: `q(3,4) = 9` with displacement `5`, while `q(3,9) = 8`, not `4`. So row 3 is not a
Wythoff-style involution for any obvious ternary analogue, and no explicit description of row 3
was obtained. That is the missing input.

## Named obstructions, with the case that closes each

**Value surjectivity of row 3** was reached at the level of an argument that was not compiled:
supposing a value `y` omitted, injectivity gives a bound `N` after every occurrence of a value
at most `y`; at a late row-2 record maximum the finitely many translates below `N` exceed `y`
while those at least `N` have larger values and positive shifts, so `y` is available and the
mex is at most `y`.

**Signed-difference surjectivity** is unresolved, with two handles closed:

| handle | first failure | the numbers |
| --- | --- | --- |
| third-translate diagonal fairness | `j = 1` | `q(3,1) = 3`, difference `2`; the candidate value `2` for the missing difference `1` is blocked by `q(3,0) + q(2,1) − q(2,0) = 2` |
| row-3 Wythoff pairing | `j = 7` | `q(3,6) = 7` would require value `6`, forbidden by the translate `q(3,4) + q(2,7) − q(2,4) = 6`; actual `q(3,7) = 11` |

Neither is a refutation: the difference `1` does occur, at `j = 6`. All the numbers above were
recomputed independently from Algorithm 1 and agree.

## What a finite computation can and cannot see here

Over 260 columns all 21 pairs of rows 1 through 7 have pairwise distinct differences — the "at
most once" half. The other half is a limit statement: on a prefix the rows are not `{0,…,n−1}`
and the difference sets have gaps, because small values arrive late. Only the proven pair
`(1,2)` has its difference set filling an interval at that width. Finite computation here is
evidence of no counterexample, never of the claim.

## Three descriptions of row 3 that are ruled out

Probes run after the seat returned, over 300 to 400 columns. All three are negative, and they
are recorded because each closes a direction a later attempt would otherwise try.

**Row 3 is not an involution.** Not merely at one point: 222 of 300 positions violate
`q(3, q(3,j)) = j`. Its cycle structure under iteration is irregular — orbits of length
1, 2, 2, 3, 3, 2, 13, 10, 11, 2, 1, 1, 5, 2 among the first fourteen from `j < 120`. No
ternary analogue of the row-2 Wythoff pairing describes it.

**The up-set is not the upper Wythoff sequence.** With `A(n) = ⌊nφ⌋` and `C(n) = ⌊nφ²⌋`, which
partition the positive integers by Rayleigh, over `[1,400)` there are 247 elements of `A` and
152 of `C`, and row 3 has 246 ascents, 153 descents and no fixed point. The relation is
containment, not equality: `C ⊆ up` with the single exception `j = 5`, and `down ⊆ A` with one
exception. So `up = C ⊔ (A ∩ up)` where `A ∩ up` has 95 elements.

**Those 95 positions are not a Beatty sequence.** Their indices within `A` begin
1, 3, 4, 8, 9, 11, 14, 16, 18, 21, 23, 26, 27, 29, 36, 40, 43, 45. Against `⌊nφ⌋` the overlap is
21 of 39, against `⌊nφ²⌋` 10 of 38, against `⌊2n⌋` and `⌊1.5n⌋` 15 of 39 — no better than
chance. The splitting inside the lower Wythoff sequence is not of Beatty type.

Taken together: the sign pattern of row 3 is governed by the Wythoff partition only at the
coarse level, and the refinement inside `A` is something else. A further attempt should look for
the explicit description elsewhere than in this family.

## Object status

Pinned Mathlib has `mex` only in the ordinal and cardinal development, and no difference matrix
or orthogonal array. This repository has `mex` as Grundy values in `D5/S1/Words/BitDeletionGrundy`
and `D5/S0/Certificates/Games/CrimGrundyRefutation`, and 117 modules mentioning Zeckendorf, but
no declaration for this construction.

## Verified locator

- URL: https://arxiv.org/abs/2503.19696
