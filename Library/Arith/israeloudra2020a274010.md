---
bibkey: israeloudra2020a274010
authors: Robert Israel; Ridouane Oudra
year: 2020
title: "OEIS A274010: the Boris Stechkin function and an adjacent divisor-count formula"
doi: null
url: https://oeis.org/A274010
claim: "Conjecture: a(n) = tau(n) + tau(n-1) - 2, for n>=2."
strata_touched:
  - D5/S3/Arith/StechkinFunctionDivisorCount
license: citation-only
triage: anchor
---

# OEIS A274010 and the Stechkin function

Robert Israel's 2016 entry defines the Boris Stechkin function `a(n)` as the
number of integers `m` with `2 <= m <= n` for which `m-1` divides the floor of
`n(m-1)/m`. Ridouane Oudra added the adjacent divisor-count conjecture on
February 28, 2020:

> Conjecture: a(n) = tau(n) + tau(n-1) - 2, for n>=2.

Here `tau` is the number of positive divisors. Natural-number Euclidean
division realizes the floor in the defining predicate. For `n >= 2`, both
`n` and `n-1` have the divisor one, so the sum of their divisor counts is at
least two. Consequently the subtraction-free equality with two added to the
left is equivalent to the displayed integer-subtraction formula.

## Verified locator

- URL: https://oeis.org/A274010
- `%I` (verbatim): A274010 #19 Mar 01 2020 12:13:16
- `%N` (verbatim): Boris Stechkin function: a(n) is the number of m with 2 <= m <= n and floor(n(m-1)/m) divisible by m-1.
- `%F` (verbatim): Conjecture: a(n) = tau(n) + tau(n-1) - 2, for n>=2. - _Ridouane Oudra_, Feb 28 2020
- `%A` (verbatim): _Robert Israel_, Jun 06 2016

## Search boundary

The entry has no settlement line. Its bibliography predates the conjecture,
and its hyperlink section contains a table rather than a proof source. The
issue registration records zero exact arXiv hits for the phrase "Stechkin
function" with positive-control searches, and zero exact repository or pinned
Mathlib hits for the sequence name and formula. Those bounded searches do not
establish global priority or exclude differently indexed results.
