---
slug: partition-weighted-sum-reversal
bibkey: wiseman2023a362559
doi: null
url: https://oeis.org/A362559
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/PartitionWeightedSumReversal.result
---

# Reversal and the Weighted Sum of a Partition

## Problem

OEIS A362559 counts the integer partitions of `n` whose one-based weighted sum is divisible
by `n`, and fixes the reading in its own comment:

> The (one-based) weighted sum of a sequence (y_1,...,y_k) is Sum_{i=1..k} i*y_i. This is
> also the sum of partial sums of the reverse.

The next comment line, at revision #18 of Apr 29 2023, is the question:

> Conjecture: A partition of n has weighted sum divisible by n iff its reverse has weighted
> sum divisible by n.

The identical line stands on A362560, which counts the complementary partitions, at
revision #6 of the same date. Both are by Gus Wiseman, Apr 24 2023, and both still carry
the word `Conjecture`.

## Motivation

The frozen theorem `D5/S3/Combinatorics/PartitionWeightedSumReversal.result` settles the
comment for every `n` and every partition.

## Gap

Issue 9506 records the screen carried out before the work. A362559 and A362560 appear
nowhere under `Problems/`, `D5/` or `docs/` in this repository. They appear as two
`note-only` rows in the 2026-09-10 triage record in `Library/Words/`, where the same
identity was noted and the rows were set aside on the ground that what remained was
reversal of a sum plus divisibility algebra. That disposition is reversed here: the
shortness of an argument is not a reason to leave a named external conjecture unjudged.

The cross-references A362558, A264034, A304818 and A318283 carry no proof of the sentence.
A web search for a published proof returned only unrelated literature on divisibility of
weighted `k`-regular partitions. Citation indices were not exhaustively reachable, so this
is a bounded negative finding.

## Route

For a finite list `y` of naturals of length `k`, write `W y` for its one-based weighted sum.
One identity carries everything:

    W y + W y.reverse = (k + 1) * (sum of y).

Reindexing the reversed sum by `j = k + 1 - i` turns `W y.reverse` into
`Sum_{j=1..k} (k+1-j) * y_j`. Adding it termwise to `W y = Sum_j j * y_j` leaves
`Sum_j (k+1) * y_j`, which is `(k+1)` times the total.

On a partition of `n` the total is `n`, so the right-hand side is a multiple of `n`, and `n`
divides one of the two weighted sums exactly when it divides the other. The entry's own
worked example is this identity at `k = 4` and `n = 9`: the weighted sum of `(4,2,2,1)` is
`18`, that of `(1,2,2,4)` is `27`, and `18 + 27 = 45 = 5 * 9`.

The formal proof takes the recursion `W (x :: t) = x + W t + (sum of t)`, which is the
one-based weighted sum written without indices, proves
`W (l ++ [x]) = W l + (length l + 1) * x` by induction on `l`, and then the displayed
identity by induction on `y`.

**What the hypothesis does.** Neither the weak decrease of the parts nor their positivity
is used; the identity holds for every finite list of naturals. The statement carries the
partition hypothesis so that it corresponds to the sentence on the entry, and that
hypothesis does no work in the proof. This is recorded rather than hidden.

## Falsifier

A different position convention would give a different weighted sum: if positions were
counted from zero, the two sums would add to `(k-1)` times the total and the equivalence
would fail. The entry's worked example pins the one-based reading. Reading the reverse of a
partition as anything other than the same parts in the opposite order would also break the
correspondence.

## Evidence

Every partition of `n` for `n = 1..40` was enumerated and both weighted sums computed. The
identity has no failure and the divisibility equivalence has no failure over that range.
The resulting counts reproduce the A362559 data line term by term over all 40 published
terms, beginning `1, 1, 2, 1, 2, 3, 3, 3, 5, 4, 5, 7`.

## Triage

`theorem`; Tier 1 named external open question, preregistered in issue 9506 before the work,
with the proof shape predicted there as `bind-only` and reported as measured. The
computational use is `none`: no declaration is a bounded enumeration, a checker, a numeric
reduction or a certified instance, and the delivered statement is universally quantified
over every `n` and every partition.

## ASSUMED-UNVERIFIED

The literature screen is bounded. Both entries were read in full at the revisions above and
their cross-references were checked; a search for a published proof returned nothing on
point. Citation indices and printed sources were not exhaustively reachable, so no worldwide
priority claim is made. The weight of the result is stated plainly: the mathematics is one
identity, and what is settled is that the sentence had stood unjudged on two entries since
April 2023.
