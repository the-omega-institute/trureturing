---
slug: cigler-partial-theta-hankel
bibkey: cigler2024partialtheta
doi: 10.48550/arXiv.2407.05768
url: https://arxiv.org/abs/2407.05768v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/PartialTheta/PartialThetaHankel.result
---

# Hankel Determinants of Backward Shifts of Partial Theta Coefficients

## Problem

Johann Cigler, *Hankel determinants of backward shifts of the coefficients of a partial theta function*,
arXiv:2407.05768v2, Section 1, the Conjecture after equation (2): with a(s, q) = q^{binom(s,2)} for s ≥ 0 and
a(s, q) = 0 for s < 0, D_{−m,N}(q) = det(a(−m + i + j, q))_{0≤i,j<N}, and r_{m,n}(q) defined by
D_{−m,n+m+1}(q) = (−1)^{binom(m+1,2)} r_{m,n}(q) q^{m binom(n,2)} D_{0,n+1}(q),

> The functions r_{m,n}(q) are monic polynomials with integer coefficients with deg r_{m,n}(q) = mn(n + m + 2)/2 which
> satisfy r_{m,n}(1) = 1 and r_{m,n}(0) = (−1)^{mn}.

The paper proves the cases m = 1 and m = 2.

## Motivation

The theorem `D5/S3/Combinatorics/PartialTheta/PartialThetaHankel.result` establishes all four assertions for every
m, n ≥ 0, together with D_{0,n+1}(q) ≠ 0, so that r_{m,n} is determined by (2).

## Gap

Pre-registration issue 12580 records the literature screen: web, GitHub and repository searches found no proof for
general m; Cigler's later work on the same sequences settles a different conjecture quoted in the paper's Appendix.
This is a bounded negative finding.

## Route

1. D_{0,n+1}(q) is a Vandermonde determinant in q⁰, q¹, …, qⁿ times a monomial, hence a monomial times
   ∏_{d=1}^{n} (q^d − 1)^{n+1−d}, which is nonzero.
2. After removing row and column monomials, D_{−m,n+m+1}(q) is a generalized Vandermonde determinant: an alternant in
   independent variables x_r evaluated at x_r = q^r.
3. Every such alternant is divisible by the Vandermonde product with an integral symmetric quotient, so r_{m,n} is an
   integer polynomial in q.
4. Among the terms of the quotient a unique one has the highest q-degree, with coefficient 1, giving monicity and the
   degree mn(n + m + 2)/2; the unique lowest term gives r_{m,n}(0) = (−1)^{mn}.
5. At q = 1 the Vandermonde factors vanish; letting the variables coalesce turns the quotient into a ratio of
   confluent determinants, which evaluates to 1.

## Falsifier

The statement would fail if the normalizing monomial in (2) were misread, if two terms of the quotient shared the
highest degree, or if the coalescence at q = 1 changed the sign.

## Evidence

An independent referee implementation checked all four assertions and the intermediate determinant identities
exactly for m ≤ 7 and n ≤ 6, and agreement with the paper's printed examples and its theorems for m = 1, 2.

## Triage

`theorem`; the statement is the Section 1 Conjecture of arXiv:2407.05768v2, quantified over all m, n ≥ 0.

- Proved (formalized): r_{m,n}(q) is a monic integer polynomial of degree mn(n + m + 2)/2 with r_{m,n}(1) = 1 and
  r_{m,n}(0) = (−1)^{mn}, for every m, n ≥ 0.
- Proved (formalized): D_{0,n+1}(q) ≠ 0, through the Vandermonde evaluation.
- Open: the paper's recurrences for r_{m,n} in the general case and a combinatorial interpretation of the
  coefficients of r_{m,n}.

## ASSUMED-UNVERIFIED

The literature screen is limited to the web, GitHub and repository searches recorded above.
