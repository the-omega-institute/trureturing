---
slug: oeis-a402341-hussain-central-coefficient-valuation
bibkey: hussain2026a402341
doi: null
url: https://oeis.org/A402341
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/BinomialBases/HussainA402341CentralCoefficientValuation
---

# Binary valuation of the even central coefficients of A402341

## Problem

Sajid Khan Hussain, OEIS A402341, revision 13, COMMENTS (`%C`):

> Conjecture: for even n, the 2-adic valuation of a(n) equals A000120(15*n/2). Verified for n <= 1500.

For a natural number n, let a(n) be the coefficient at degree
`floor(15*n/2)` of `(1 + x + ... + x^15)^n` over the natural numbers.
The conjecture is that the exponent of two in a(n) is the binary digit
sum of `15*n/2` for every even natural n, including zero.

## Motivation

Parity distinguishes odd from even central coefficients. The valuation
conjecture determines the exact power of two dividing each even-indexed
coefficient. [Preregistered claim](https://github.com/the-omega-institute/trureturing/issues/34422)

## Gap

The pinned revision and the public entry present the valuation as a
conjecture. The entry gives a parity proof and a central-binomial expansion.
The exact valuation requires controlling the divisibility of the other
terms of that expansion. The preregistration records exact-identifier
searches across GitHub, arXiv and repository sources and related work on
weighted compositions and asymptotic extended binomial coefficients.
[Primary source](https://raw.githubusercontent.com/oeis/oeisdata/85deec2fc1f93c9f10dee75501f7059dab264784/seq/A402/A402341.seq)
[Preregistration](https://github.com/the-omega-institute/trureturing/issues/34422)

## Route

1. Expand the geometric polynomial over the integers in the basis
   `x^j(1+x)^(15-2j)`. Write H for the polynomial with the resulting
   eight coefficients. At every degree j its coefficient is divisible
   by `2^s(j)`, where s is the binary digit sum, and its constant term is 1.
2. Group the terms in each coefficient of H squared into off-diagonal
   pairs and a possible diagonal term. The carry inequality
   `s(a+b) <= s(a)+s(b)` handles the pairs. The identity `s(2a)=s(a)`
   and positivity of `s(a)` for positive a handle the diagonal.
   Every positive-degree coefficient is divisible by `2^(1+s(j))`.
   This divisibility is closed under products.
3. For n = 2k, the central coefficient at m = 15k is
   `binom(2*m,m)` plus the contribution from positive degrees of
   `(H^2)^k`. The latter is divisible by `2^(1+s(m))` by the same
   carry inequality. The central binomial term has valuation exactly
   `s(m)`, so the correction preserves that valuation.

## Falsifier

An even natural n with a vanishing central coefficient or a valuation
different from the binary digit sum at the stated degree would contradict
the formal result.

## Evidence

- Formal declaration `D5/S3/Combinatorics/BinomialBases/HussainA402341CentralCoefficientValuation.result`.
- Its statement gives positivity and exact valuation of the literal
  polynomial coefficient for every even natural index. At index zero the
  coefficient is 1, with valuation and binary digit sum both zero.
- The axiom closure is `propext`, `Classical.choice`, and `Quot.sound`.

## Triage

`theorem`. Proved for the full domain by
`D5/S3/Combinatorics/BinomialBases/HussainA402341CentralCoefficientValuation.result`.

### What the settlement shows

- Proved as part of the same result. The first central-binomial term
  controls the valuation because the aggregate correction has one
  extra factor of two. The proof handles the empty product at zero.
- The internal divisibility argument applies to an integral change-of-basis
  polynomial with constant term one whose square satisfies the stated
  positive-degree divisibility, when its lift gives the source coefficient.
  Verifying those hypotheses for other geometric lengths is open here.
- The exact valuation implies evenness for every positive even index,
  since the central degree is positive. The source's separate parity
  criterion also covers odd indices. The asymptotic formula is independent
  of the even-index valuation argument.

## ASSUMED-UNVERIFIED

The literature search is bounded to the sources and searches described
above. Exhaustive historical priority is unverified.
