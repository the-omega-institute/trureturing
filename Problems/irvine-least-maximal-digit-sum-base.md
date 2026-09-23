---
slug: irvine-least-maximal-digit-sum-base
bibkey: irvine2026a394431
doi: null
url: https://oeis.org/A394431
triage: theorem
motivation_gids:
  - D5/S1/Digit/MaxDigitSumBase.result
---

# The Least Base Maximizing the Digit Sum of n Is ceiling((n+1)/2) for n > 8

## Problem

OEIS A394431, by Jean-Marc Rebert, Mar 20 2026:

> The smallest base b < n where the sum of the digits for the number n in the base b is the
> largest, with 1 < b < n and a(1) = a(2) = 1.

The formula line carrying the question, by Sean A. Irvine, Mar 25 2026:

> Conjecture: a(n) = ceiling((n+1)/2) for n>8.

## Motivation

The frozen theorem `D5/S1/Digit/MaxDigitSumBase.result` settles the conjecture for every `n > 8`,
stating both that no base in `1 < b < n` beats `ceiling((n + 1) / 2)` and that every smaller base
does strictly worse.

## Gap

Issue 9617 records the screen carried out before the work. The A-number appears nowhere under
`Problems/`, `D5/`, `Library/` or `Blueprint/` in this repository, nor in the three screening
records, nor under `FormalConjectures/OEIS/` in google-deepmind/formal-conjectures. The entry records
no proof and no reference. A catalogue search by the terms returns only this entry, and by the
largest digit sums only the generic entry for `floor(n / 2)`. Web and MathDB queries returned no
paper or note giving the result. This is a bounded negative finding.

## Route

Write `s_b(n)` for the base-`b` digit sum and `b0 = floor(n / 2) + 1`, which equals
`ceiling((n + 1) / 2)`.

**One.** If `b` is a base with `n < 2 * b` and `b < n`, then `n / b = 1` and `n mod b = n - b`, so
`s_b(n) = n - b + 1`. In particular `s_b0(n) = n - floor(n / 2)`, and every larger base gives less.

**Two.** Every digit sum is at most its argument, `s_b(q) ≤ q`. If `q ≥ b` then expanding once more,
`s_b(q) = (q mod b) + s_b(q / b) ≤ (q mod b) + q / b`, while `q = (q mod b) + b * (q / b)` with
`q / b ≥ 1`; hence `s_b(q) + (b - 1) ≤ q`.

**Three.** Let `2 ≤ b` with `2 * b ≤ n` and `n > 8`. Write `n = q * b + r`, so `q ≥ 2`, `r < b` and
`s_b(n) = r + s_b(q)`. If `q ≥ b`, step two gives `2 * s_b(n) ≤ 2 * r + 2 * q - 2 * (b - 1)`, which
is below `r + b * q = n` because `r ≤ b - 1` and `b ≥ 2`. If `q < b`, then `b ≥ 4`, because `b = 2`
or `b = 3` with `q < b` would force `n ≤ 8`; then `2 * s_b(n) ≤ 2 * r + 2 * q < r + b * q`, since
`(b - 2) * q ≥ 2 * b - 4 > b - 1 ≥ r`. In both cases `2 * s_b(n) < n`.

**Four.** Step three gives `s_b(n) < n - floor(n / 2) = s_b0(n)` for every base at most half of
`n`, and these are exactly the bases below `b0`; step one covers the bases from `b0` up to `n - 1`.
So `b0` attains the maximum and every smaller base falls strictly short.

The content sits in steps two and three; step one is the two-digit expansion.

## Falsifier

The statement would fail at `n = 8`, where `s_3(8) = 4 = s_5(8)` makes `3` the least maximizing
base; this is the equality case `b = 3`, `q = r = 2` of step three, and the conjecture excludes it by
requiring `n > 8`. Reading `ceiling((n + 1) / 2)` as `floor((n + 1) / 2)` would give `n / 2` for even
`n`, a base with two digits `2, 0`, whose digit sum `2` is not maximal for `n > 8`.

## Evidence

The least maximizing base was recomputed from the definition for every `n` from `1` to `1499` and
agrees with the entry's b-file term by term; the b-file's 10000 terms satisfy the conjecture at every
`n > 8`. The strict gap between the largest digit sum over bases at most `n / 2` and
`ceiling(n / 2)` was checked for every `n` from `9` to `19999`, with no exception, and the exception
at `n = 8` was reproduced.

## Triage

`theorem`; Tier 1 named external open question from 2026, preregistered in issue 9617 before the
work. The computational use is `none`: no declaration is a bounded enumeration, a checker, a numeric
reduction or a certified instance, and the delivered statement is universally quantified over every
`n > 8`.

## ASSUMED-UNVERIFIED

The literature screen is bounded. The entry was read in full and records no proof and no reference
to one; the conjecture has stood since March 2026. Citation indices and printed sources were not
exhaustively reachable, so no worldwide priority claim is made. The weight is stated plainly: the
argument is elementary, and what is settled is that the sentence sat on the entry unjudged.
