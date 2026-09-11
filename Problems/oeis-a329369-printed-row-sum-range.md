---
slug: oeis-a329369-printed-row-sum-range
bibkey: oeis2024a329369
doi: null
url: https://oeis.org/A329369
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm
---

# The printed index range of the sixth A329369 sum

## Problem

Write a(n) for A329369 and T(n,k) for the A373183 row coefficients. Mikhail
Kurkov printed on June 05 2024 the assertion that

  a(2^m*n + q) = Sum over i from A001511(n+1) to A000120(n)+1 of
                 T(n, i) * a(2^m*(2^(i-1)-1) + q)

holds for n at least zero, m at least zero, and q at least zero. The same
assertion appears in A373183 as its second conjecture. The question is whether
the printed range for q is correct.

## Motivation

The two entries define a(n) by a(2n+1)=a(n) and, for positive n,
a(2n)=a(n)+a(n-2^f(n))+a(2n-2^f(n)) with f the two-adic valuation, and they
define T through the row polynomials R(2n+1,x)=x*R(n,x),
R(2n,x)=x*(R(n,x+1)-R(n,x)), R(0,x)=x. Both definitions are already carried in
this repository, so the printed sum can be evaluated against them directly.

## Gap

The sum is a decomposition of the index into a multiple of 2^m and a remainder
q. Such a decomposition normally carries the restriction that q is below 2^m,
and the printed text carries no such restriction. Nothing in the entry says
which reading is intended.

## Route

The rows at a positive power of two have the closed form
R(2^k, x) = (2^k - 1)*x + 2^k*x^2, proved by induction: the difference operator
sends the coefficient pair (a, c) to (a + c, 2c), and the row at index two is
x + 2x^2. Reading off coefficients gives T(2^k,1) = 2^k - 1 and T(2^k,2) = 2^k,
while A001511(2^k+1) = 1 and A000120(2^k) + 1 = 2 pin the summation range to
the two indices one and two. Evaluating at m equal to zero and q equal to one
makes the left side a(2^k+1) = 2^k - 1 and the right side
(2^k - 1) + 3*2^k = 2^(k+2) - 1. These are never equal.

## Falsifier

An index triple with q at least 2^m at which the two sides agree would not
disturb the theorem, which asserts only that specific triples differ. A proof
that the two sides agree for every q at least zero would contradict it.

## Evidence

- Module: `D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm.lean`.
- Closed form: `R_two_pow`.
- Counterexample family: `printed_recurrence_ne_at_two_pow`.
- Closed negation of the printed reading: `not_kurkovRowRecurrence`.
- The defining recurrences are derived, not assumed: `b_zero`, `b_odd_index`,
  `b_even_index`, the last from the frozen row identity in
  `D5/S1/Digit/DyadicRowPolynomialRecurrence`.

## Triage

`theorem`. Only the printed reading with q unrestricted is settled, and it is
settled in the negative. The reading in which q is below 2^m is a different
assertion; it is not settled here and stays open. An arithmetic sweep over
indices below 2^18, with n below 256 and m at most ten, found 2781 differing
triples for the printed reading and every one of them had q at least 2^m, while
the restricted reading produced none. That sweep is evidence about a bounded
window, not a proof.

## ASSUMED-UNVERIFIED

Whether the unrestricted range is an oversight rather than the intended
assertion is not established; only the printed text is cited. No search for a
published correction or for prior notice of this range was made, so priority is
not claimed.
