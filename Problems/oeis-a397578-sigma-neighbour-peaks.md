---
slug: oeis-a397578-sigma-neighbour-peaks
bibkey: ratushnyak2026a397578
doi: null
url: https://oeis.org/A397578
triage: theorem
motivation_gids:
  - D5/S3/Arith/Robin/SigmaNeighbourPeak.result
---

## Problem

Ratushnyak's OEIS A397578 defines a(n) as the least k satisfying sigma(k) > n sigma(k-1) and sigma(k) > n sigma(k+1), and states: “Conjecture: a(n) exists for all n.” The exact assertion is preregistered in [#14990](https://github.com/the-omega-institute/trureturing/issues/14990).

Writing $\sigma(k)=\sum_{d\mid k}d$, the closed claim is

$$\forall n\in\mathbb N,\ \exists k\in\mathbb N,\quad k\ge2\ \land\ n\sigma(k-1)<\sigma(k)\ \land\ n\sigma(k+1)<\sigma(k).$$

The natural domain includes zero. Existence of a witness entails existence of a least witness by well-ordering.

## Motivation

The assertion asks whether divisor-sum peaks can simultaneously exceed both neighbours by an arbitrarily large factor. Primorials contain every small prime; their neighbours contain none, separating the sources of large and small abundancy.

## Gap

The supplied literature reading identifies the OEIS conjecture without a proof. Erdős (1936) proved that $\sigma(n+1)\ge\sigma(n)$ holds on a set of density one half. Erdős–Győry–Papp proved that chains of comparisons among $\sigma(n+1),\ldots,\sigma(n+4)$ occur infinitely often. Neither result gives the simultaneous arbitrary-ratio assertion. These are supplied preregistration readings, not a fresh external search or an exhaustive originality claim.

## Route

Let $P=\prod_{p\le x}p$ for $x\ge4$. The identity $\sigma(P)/P=\sum_{d\mid P}1/d$ includes every term $1/p$ with $p\le x$. Divergence of the prime reciprocal series therefore gives a threshold with $\sigma(P)>6nP$.

For $m=P-1$ or $m=P+1$, no prime at most $x$ divides $m$. The product of the distinct prime factors of $m$ divides $m$, and each factor is at least four. Mathlib's primorial bound gives

$$4^{\omega(m)}\le m\le4^x+1<4^{x+1},$$

so $\omega(m)\le x$. Prime-power geometric sums give

$$\frac{\sigma(m)}m\le\prod_{p\mid m}\frac p{p-1}\le(1+1/x)^{\omega(m)}\le(1+1/x)^x\le e<3.$$

Thus $n\sigma(P-1)<\sigma(P)$ and $n\sigma(P+1)<\sigma(P)$, since $P+1\le2P$. For $n=0$, positivity of $\sigma(P)$ supplies the strict inequalities directly.

## Falsifier

An index n for which every k fails at least one of the two strict inequalities would refute the assertion. A mismatch in the sum-of-divisors convention, loss of strictness, or an invalid bound on either neighbour's prime factors would invalidate the proposed proof. A prior resolution of the exact assertion would affect open-problem eligibility without changing the mathematics.

## Evidence

`D5.S3.Arith.Robin.SigmaNeighbourPeak.result : claim` proves the exact quantified assertion. Private lemmas establish the prime-power bound, multiplicative abundancy estimate, rough-number bound, primorial growth and neighbour roughness. The reciprocal divisor identity is reused from `GoldenResourceOptimalInteger.reciprocal_divisor_sum`. The matching Blueprint result node declares a Proved resolution of this slug. The implementation report supplies the scoped build result.

## Triage

- [proved] For every natural n, some primorial k dominates both adjacent divisor sums by factor n.
- [open] The growth rate of the least witness a(n), and whether a(n) is always a highly abundant number.

## ASSUMED-UNVERIFIED

No fresh network search was performed because this implementation seat has no network. The OEIS source and literature-gap readings are supplied by preregistration. Completeness of the literature search and exclusive priority remain unverified. The proof asserts existence, with no growth-rate or highly-abundant-minimizer conclusion.
