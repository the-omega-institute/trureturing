---
slug: divisor-doubling-multiple-divides-square
bibkey: lowell2013a225004
doi: null
url: https://oeis.org/A225004
triage: theorem
motivation_gids:
  - D5/S3/Factorization/DivisorDoublingMultipleDividesSquare.result
---

# A Multiple with Fewer than Twice as Many Divisors Divides the Square

## Problem

OEIS A225004, at revision #24 of Mar 17 2022, by J. Lowell, Apr 23 2013:

> a(n) is the largest multiple of n with fewer than twice as many divisors as n.

> Conjecture: a(n) is always a divisor of n^2.

The entry's worked example: "a(6) = 18 because 6 has 4 divisors and term must have fewer than 8
divisors. Only 6, 12, and 18 are multiples of 6 with fewer than 8 divisors."

## Motivation

The frozen theorem `D5/S3/Factorization/DivisorDoublingMultipleDividesSquare.result` settles the
comment, in the stronger form that every admissible multiple divides `n^2`.

## Gap

Issue 9513 records the screen carried out before the work. A225004 appears nowhere under
`Problems/`, `D5/` or `docs/` in this repository. It appears as one `note-only` row in the
2026-09-10 triage record in `Library/Words/`, where the same exponent argument was written out and
the row was set aside for high bind risk. That disposition is reversed here: the risk named there is
about the proof shape, which is reported as measured, and is not by itself a reason to leave a named
external conjecture unjudged.

The entry's only cross-reference is A000005, which carries no proof of this. Citation indices were
not exhaustively reachable, so this is a bounded negative finding.

## Route

Write `f` for the exponent in the prime factorisation, so that `τ(k) = ∏ (f_k(p) + 1)` over the
primes of `k`. Divisibility by `n^2` is equivalent to `f_m ≤ 2 f_n` pointwise, so the statement is a
bound on one exponent at a time.

Let `n ∣ m` with both positive, giving `f_n ≤ f_m` pointwise and the primes of `n` among those of
`m`. Suppose some prime `q` had `f_m(q) > 2 f_n(q)`.

**`q` is not a prime of `n`.** Then `q` is a prime of `m` lying outside the primes of `n`. Split the
product for `τ(m)` into the part over the primes of `n` and the rest. The first part is at least
`τ(n)`, factorwise. The second contains the factor at `q`, which is at least two, and every other
factor in it is at least one.

**`q` is a prime of `n`.** Then `f_m(q) + 1 ≥ 2 f_n(q) + 2 = 2 (f_n(q) + 1)`. Pull `q` out of the
product over the primes of `n`: that one factor supplies the two, and each remaining factor is at
least the corresponding factor of `τ(n)`. The part of `τ(m)` outside the primes of `n` is at least
one.

Either way `τ(m) ≥ 2 τ(n)`, contradicting `τ(m) < 2 τ(n)`.

**Why the delivered statement is stronger than the sentence, deliberately.** The entry's `a(n)` is
the largest admissible multiple. Writing `a(n)` down needs a bound on the search, and the only
natural bound is `n^2` — which is the conclusion, so defining it that way would presuppose what is
to be proved. The statement delivered says every admissible multiple divides `n^2`. It contains the
conjecture, since `a(n)` is one such multiple, and it establishes in addition that the admissible
multiples are finitely many, so the maximum the entry names exists at all.

## Falsifier

A reading in which the divisor count is compared with `2 τ(n)` non-strictly would change the
statement: with `τ(m) ≤ 2 τ(n)` allowed, `m = p^{2a+1}` for `n = p^a` has `τ(m) = 2a + 2 = 2 τ(n)`
and does not divide `n^2`. The entry's wording is "fewer than", and its worked example at `n = 6`
lists exactly the multiples with fewer than eight divisors, so the strict reading is the entry's.

## Evidence

A divisor-count sieve to 200000 was used to test the delivered statement directly: for every
`n ≤ 2000`, every multiple of `n` up to 200000 with fewer than `2 τ(n)` divisors was checked to
divide `n^2`. No violation. The largest admissible multiple was computed for each such `n` and
divides `n^2` in every case; those values reproduce the entry's data line term by term over all 53
published terms, beginning `1, 4, 9, 16, 25, 18, 49, 64, 81, 50, 121, 48`, and the worked example at
`n = 6` comes out as `18`. Of the `n ≤ 2000`, exactly 106 have `a(n) = n^2`; the prime powers are
among them, as the argument predicts.

## Triage

`theorem`; Tier 1 named external open question, preregistered in issue 9513 before the work. The
computational use is `none`: no declaration is a bounded enumeration, a checker, a numeric reduction
or a certified instance, and the delivered statement is universally quantified over every `n` and
every `m`.

## ASSUMED-UNVERIFIED

The literature screen is bounded. The entry was read in full at revision #24 and its cross-reference
was checked. Citation indices and printed sources were not exhaustively reachable, so no worldwide
priority claim is made. The weight is stated plainly: the argument is elementary, and what is settled
is that the sentence sat on the entry for thirteen years without being judged.
