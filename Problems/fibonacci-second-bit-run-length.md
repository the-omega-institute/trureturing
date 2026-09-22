---
slug: fibonacci-second-bit-run-length
bibkey: cicuttin2016a272170
doi: null
url: https://oeis.org/A272170
triage: theorem
motivation_gids:
  - D5/S3/Arith/FibonacciSecondBitRunLength.result
---

# Runs in the Second Binary Digit of the Fibonacci Numbers

## Problem

OEIS A272170 is the sequence of second most significant binary digits of the Fibonacci
numbers exceeding one. Its COMMENTS section carries, at revision #34 of Dec 08 2025:

> It is conjectured that there are no more than two consecutive "0's" or "1's" (tested up to
> n=10^5). The sequence looks quasiperiodic and its Fourier spectrum seems to have a fractal
> structure. - _Andres Cicuttin_, Apr 21 2016

Writing `s(m) = m / 2 ^ (size m - 2) % 2` for that digit, the assertion is

    ∀ n ≥ 3,  ¬ ( s(F n) = s(F (n+1)) ∧ s(F (n+1)) = s(F (n+2)) ).

## Motivation

The frozen theorem `D5/S3/Arith/FibonacciSecondBitRunLength.result` proves it.

## Gap

Issue 9441 records the screen carried out before the probe. The entry was read in full at
revision #34: the comment stands with no proof and no reference to one.

Two recent efforts settle OEIS conjectures in bulk, and the sibling comment at A271591, the
same assertion for the tribonacci numbers, was proved by both: the entry now carries a note of
May 28 2026, a Lean file in `google-deepmind/alphaproof-nexus-results` and a proof at page 18
of arXiv:2608.11941. The Fibonacci case is therefore cleared against both by membership rather
than by reading prose. A272170 does not appear among the 492 statements of
`epoch-research/LeanOpenProblems` at `apn/data/oeis/Isolated/`, in any of the 25 run
directories of `epoch-research/LeanOpenProblems-results`, among the 38 Lean files of
`google-deepmind/alphaproof-nexus-results/APNOutputs/OEIS/`, or anywhere in the text of
arXiv:2608.11941. A271591 appears in all four, which is the control that these checks can see
a settlement when there is one.

Reading the entry is on its own not sufficient: of twelve settled statements sampled from that
corpus, five carry no note of the settlement on their OEIS page, two of them settled in all
nineteen attempts. Citation indices were not exhaustively reachable, so this remains a bounded
negative finding.

## Route

The digit becomes arithmetic once the number is bracketed between consecutive powers of two.
For `m ≥ 2` take `L = size m - 2`; then `2 · 2^L ≤ m < 4 · 2^L`, and inside such a bracket the
second digit is one exactly when `3 · 2^L ≤ m`, because the quotient `m / 2^L` is then `2` or
`3`. The bracket used need not be the one built from `size m`: any `L` with
`2 · 2^L ≤ m < 4 · 2^L` reads the same digit, which is what lets the argument move between
`L`, `L+1` and `L+2` without tracking sizes.

The second ingredient is a two-sided bound on consecutive Fibonacci numbers,

    8 · F n ≤ 5 · F (n+1)     and     8 · F (n+1) ≤ 13 · F n        for n ≥ 5.

Its content is that the interval `[8/5, 13/8]` is carried into itself by `x ↦ 1 + 1/x`, which
is the step the Fibonacci ratio takes. Each half of the bound is what proves the other half at
the next index, so the pair is a single induction; both ends are attained at `n = 5`, where
`F 5 = 5` and `F 6 = 8` give `40 ≤ 40` and `64 ≤ 65`. A one-sided bound does not work: pushing
the upper bound forward needs a ratio above `8/5`, and the cruder lower bound `3 F n < 2 F (n+1)`
only supplies `3/2`.

Write `a = F n`, `b = F (n+1)`, `c = F (n+2) = a + b`, and `t = 2^L` for the bracket of `a`.

**Three ones.** From `3t ≤ a < 4t` the bounds give `2b > 3a ≥ 9t` and `8b ≤ 13a < 52t`, so
`4t < b < 8t` and `b` sits one bracket up. Its digit is one exactly when `6t ≤ b`. Then
`2c = 2a + 2b < 8t + 13t = 21t`, while `c` sits two brackets up, where a one needs `2c ≥ 24t`.
So the third digit is zero.

**Three zeros.** From `2t ≤ a < 3t` the bounds give `3t < b` and `8b ≤ 13a < 39t`. If `b < 4t`
then `b` shares the bracket of `a` and `b > 3t` already makes its digit one. Otherwise
`4t ≤ b`, so `c = a + b ≥ 6t` while `8c ≤ 21a < 63t < 64t`, putting `c` in the bracket
`[4t, 8t)` with `c ≥ 6t`, so the third digit is one.

The cases `n = 3, 4` are checked directly.

## Falsifier

A single index with three equal digits would settle it the other way. The digit function was
matched term by term against the entry's published terms
`0,1,0,0,1,0,0,1,0,0,1,0,0,1,1,0,0,1,0,0,1,0,0,1,0,0,1,1,0,0,1,0,0,1` — all 34 agree — and
then run on exact integers to `n = 60000`, where the longest run of either digit is two.

## Evidence

The conjecture's own wording points at quasiperiodicity and a fractal Fourier spectrum, which
suggests an equidistribution argument. None is needed: the ratio bound plus the bracket
characterisation reduce the whole statement to integer inequalities. That is why the target
was reachable at hour scale.

## Triage

`theorem`; Tier 1 named external conjecture on an OEIS comment line, preregistered in issue
9441 before the probe. The admission basis is `escape-witness` with
`proof_shape: content`. The module reports `utility: none`: no declaration in it is a bounded
enumeration, a checker, a numeric reduction or a certified instance, and the statement is a
universally quantified fact rather than a finite computation.

## ASSUMED-UNVERIFIED

The literature screen is bounded: the OEIS entry at revision #34 was opened, and membership
was checked against the two bulk corpora named in the Gap; citation-index result pages were
not exhaustively reachable, so no worldwide priority claim is made. The annotation-lag reading
rests on a sample of twelve, not on the whole corpus.

The numerical range `n ≤ 60000` is below the `10^5` the comment reports and was run to check
the digit implementation against the published terms, not to extend the verified range; it is
superseded by the recorded proof.
