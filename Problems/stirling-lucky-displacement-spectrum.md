---
slug: stirling-lucky-displacement-spectrum
bibkey: colmenarejo2024lucky
doi: 10.48550/arXiv.2403.03280
url: https://cs.uwaterloo.ca/journals/JIS/VOL27/Tenner/tenner12.html
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/StirlingLuckyDisplacementSpectrum.result
---

# Stirling Lucky Displacement Spectrum

## Problem

Colmenarejo, Dawkins, Elder, Harris, Harry, Kara, Smith and Tenner, *Journal of
Integer Sequences* 27 (2024), Article 24.6.7, study Stirling permutations as
parking preference lists. Definition 4 reads: "A permutation of the multiset
{1, 1, 2, 2, 3, 3, . . . , n, n} is a Stirling permutation of order n if every
value j appearing between the two instances of i satisfies j > i." Definition 39
sets `dis(w) = (d(1), …, d(2n))`, where `d(i)` is the spot car `i` takes minus
the spot `w(i)` it prefers, so `d(i) = 0` exactly when car `i` is lucky.

Corollary 41 reads: "For every w ∈ Q_n, we have 1 ≤ |{i ∈ [2n] : d(i) = 0}| ≤ n",
so the number of nonzero entries of `dis(w)` lies in `[n, 2n - 1]`. The article
then states:

> Problem 48. Determine if, for i ∈ [n, 2n − 1], there exists w ∈ Q_n such that
> dis(w) has exactly i nonzero entries. Equivalently, can we always find a
> Stirling permutation with i unlucky cars?

## Motivation

The frozen theorem
`D5/S3/Combinatorics/StirlingLuckyDisplacementSpectrum.result` answers that
question affirmatively for every order `n ≥ 1` and every `i` in the stated
range, by an explicit word. Theorem 13 and Corollary 45 of the article already
supply the two endpoints `2n - 1` and `n`; the theorem recorded here fills in
every count between them and shows the fibres of Problem 49 are all nonempty.

## Gap

The journal article and the sole arXiv version arXiv:2403.03280v1 were opened,
together with arXiv:2410.08057, which fixes the lucky set of a general parking
function and does not treat Stirling permutations; arXiv:2507.17667, which
studies Euler--Stirling statistics and treats neither parking nor luck; and
arXiv:2508.13917. None records an answer to Problem 48, and the arXiv record
carries no version after v1. Citation-index result pages were not reachable, so
this is a bounded negative finding.

## Route

For `j` from `0` to `n - 1` let

    V(n, j) = (j+1)(j+1) (j+2)(j+2) ⋯ n n  j j (j-1)(j-1) ⋯ 1 1 ,

each value written twice in succession, the values above `j` in increasing order
followed by the values at most `j` in decreasing order. Equal letters are
adjacent, so no value stands between two occurrences of the same value and
`V(n, j) ∈ Q_n`; the letters are each of `1, …, n` twice, so the length is `2n`.

Parking keeps the occupied spots equal to one interval at every stage. The first
car takes the free spot `j + 1` and is lucky. Every later car of the increasing
block prefers a spot inside the occupied interval, because the interval has
grown by two for each pair already parked while the preference has grown by one,
so it is pushed to the spot just above the interval; after the increasing block
the occupied spots are `j + 1` through `2n - j` and exactly one car has been
lucky. In the decreasing block the first copy of a value `v` finds `v` free just
below the interval and is lucky, and the second copy is pushed to the spot just
above it, so each of the `j` pairs contributes one lucky car and the interval
grows by one at each end. The lot ends full, spots `1` through `2n`.

So `V(n, j)` has `j + 1` lucky cars and `2n - j - 1` nonzero displacement
entries. As `j` runs over `[0, n - 1]` that count runs over `[n, 2n - 1]`, and
the count `i` is realised by `j = 2n - 1 - i`.

## Falsifier

A single `(n, j)` whose word fails the Stirling condition, or whose parking
outcome has a lucky count other than `j + 1`, would invalidate the family. Two
independent checks constrain it: the article states that the displacement of any
Stirling permutation of order `n` sums to `n^2`, and that the first entry of
`dis(w)` is always zero. At `n = 3` the words `112233`, `223311` and `332211`
have displacement compositions `(0,1,1,2,2,3)`, `(0,1,1,2,0,5)` and
`(0,1,0,3,0,5)`; each begins with zero, each sums to `9`, and they carry five,
four and three nonzero entries.

## Evidence

An independent enumeration parks every `V(n, j)` for `n` from `1` to `30` and
every `j` in `[0, n - 1]`, checks the multiset and the condition on values
between equal letters directly, and confirms the lucky count `j + 1` and that
the set of attained nonzero-entry counts is exactly `[n, 2n - 1]`; there were no
mismatches. This is a check of the family, not of the theorem: the theorem is
proved for every `n`.

The two endpoints agree with the article independently. At `j = 0` the word is
`1 1 2 2 ⋯ n n`, which has one lucky car, the count Theorem 13 associates with
displacement compositions having exactly one zero entry. At `j = n - 1` the word
is `n n (n-1)(n-1) ⋯ 1 1`, which has `n` lucky cars, the maximum allowed by
Corollary 41.

## Triage

`theorem`; Tier 1 named external open problem, preregistered in issue 9275
before write-up. The admission basis is `open-problem-resolution`. The
classification is `proof_shape: content`; the escape content is the interval
occupancy invariant carried through the parking process, which is not an
instantiation, projection or normalisation of a pinned upstream statement. The
computational content classification is `none`: the delivered statement is a
theorem for every order, and the enumeration above stays outside the module.

## ASSUMED-UNVERIFIED

The literature screen is bounded: the journal article, arXiv:2403.03280v1,
arXiv:2410.08057, arXiv:2507.17667 and arXiv:2508.13917 were opened, and the
arXiv record shows no version after v1; citation-index result pages were not
reachable, so no worldwide priority claim is made.

Problem 49 of the article, which asks for the number of `w ∈ Q_n` with exactly
`k` lucky cars for `k ∈ [2, n - 1]`, is not settled here; only the nonemptiness
of those fibres follows. Problems 50 and 51, on the image and the fibres of
`w ↦ dis(w)`, are likewise untouched.

The family `V(n, j)` is one witness per count and is not claimed to be the
lexicographically first or in any way canonical among the words attaining that
count.
