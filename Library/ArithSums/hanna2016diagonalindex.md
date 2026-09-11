---
bibkey: hanna2016diagonalindex
authors: Paul D. Hanna
year: 2016
title: "OEIS A266489, A300732, A300733, A292394, and A300734: vanishing-diagonal index divisibility"
doi: null
url: https://oeis.org/A266489
claim: "A266489: G.f. A(x) satisfies: [x^n] A( x/A(x)^n ) = 0 for n>1. (C1) n divides a(n) for n>=1: A268293(n) = a(n)/n. A300732: G.f. A(x) satisfies: [x^n] A( x/A(x)^(2*n) ) = 0 for n>=1. Conjecture: n divides a(n) for n>=1. A300733: G.f. A(x) satisfies: [x^n] A( x/A(x)^(3*n) ) = 0 for n>=1. Conjecture: n divides a(n) for n>=1. A292394: G.f. A(x) satisfies: [x^n] A( x/A(x)^(n^2) ) = 0 for n>1. a(n) is divisible by n^2 for n>=1 (conjecture): A292395(n) = a(n)/n^2. A300734: G.f. A(x) satisfies: [x^n] A( x/A(x)^(2*n^2) ) = 0 for n>1. Conjecture: n^2 divides a(n) for n>=1."
strata_touched:
  - D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility
license: citation-only
triage: anchor
---

# Vanishing-diagonal index divisibility

Paul D. Hanna's entries specify the five generating equations and divisibility
conjectures quoted above. A266489 is dated February 7, 2016; A292394 is dated
September 15, 2017; A300732, A300733, and A300734 are dated March 11, 2018.
The published data in all five entries begin with constant and linear
coefficients `1,1`.

The normalized family uses `a(0)=a(1)=1` and
`[x^n] A(x/A(x)^e(n)) = 0` for `n > 1`. The literal NAMEs of A300732 and
A300733 instead print `n>=1`. At degree one, substitution by a series with
linear coefficient one preserves `a(1)=1`, so that printed boundary is
incompatible with their own data. The corresponding formal instances use
`n>1`; they do not assert the inconsistent degree-one vanishing equation.

The exponent functions are `n`, `2*n`, `3*n`, `n^2`, and `2*n^2`. A single
integer-series construction proves the normalized generating equation and
uniqueness. For every natural `k`, if `n^k` divides `e(n)` for every natural
`n`, then `n^k` divides `a(n)` for every `n>=1`. Formal differentiation of
integer powers of a unit gives the exponent factor; strong induction and
a two-case comparison of prime multiplicities provide the divisibility of
each summand in the triangular coefficient equation.

At `e(n)=n`, uniqueness identifies the constructed series with
`NegativePowerDiagonalModPrime.generatingSeries 2`. Consequently A266489's
clause C1 is proved for that existing coefficient function. Its separate
clause C2 is not part of the general index-divisibility assertion here.

## Verified locator

- URL: https://oeis.org/A266489
- URL: https://oeis.org/A300732
- URL: https://oeis.org/A300733
- URL: https://oeis.org/A292394
- URL: https://oeis.org/A300734
