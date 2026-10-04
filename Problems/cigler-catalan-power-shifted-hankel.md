---
slug: cigler-catalan-power-shifted-hankel
bibkey: cigler2023catalanpowers
doi: 10.48550/arXiv.2308.07642
url: https://arxiv.org/abs/2308.07642v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/CatalanPowerHankel/CiglerEleven.result
---

# Shifted Hankel Determinants of Odd Catalan Powers

## Problem

Johann Cigler, *Some experimental observations about Hankel determinants of convolution powers of Catalan numbers*,
arXiv:2308.07642v2, Section 2.2, Conjecture 11: with C_{r,j} = r/(2j+r) · binom(2j+r, j) for j ≥ 0, C_{r,j} = 0 for
j < 0, and D_{r,s}(N) = det(C_{r,i+j+s})_{0 ≤ i,j < N}, D_{r,s}(0) = 1, for every k ≥ 1, 0 ≤ m ≤ k+1 and n ≥ 0,
D_{2k+1,m−k+1}((2k+1)n+k) = (−1)^{kn+binom(k,2)} (2k+1)^m (n+1)^m. The shift m − k + 1 may be negative.

## Motivation

The theorem `D5/S3/Combinatorics/CatalanPowerHankel/CiglerEleven.result` establishes Conjecture 11 for every
k ≥ 1, 0 ≤ m ≤ k+1 and n ≥ 0.

## Gap

Pre-registration issue 12943 records the literature screen: the case m = 0 is equation (22) of Cigler,
arXiv:2403.11244; Fulmek, arXiv:2402.19127, proves a different conjecture of the same paper; Chern and Shi,
arXiv:2608.27208, treat conjectures of a different paper; the repository had no claim on it. This is a bounded
negative finding.

## Route

1. The coefficients C_{2k+1,t−k} are the moments ℒ(X^t p_k) of a monic orthogonal family p_j for the Jacobi
   operator with boundary weight 1 and interior weight 2, proved through the Pascal recurrence of the coefficient array.
2. For any monic orthonormal family, a shifted Hankel determinant of order N reduces to a determinant of remainders
   modulo a monic polynomial u of degree h, a fixed-size determinant independent of N.
3. With u = X^d p_k, a coordinate change on a monic basis evaluates that determinant through p_k(0) = (−1)^k.
4. Shifted Chebyshev identities give the remainders of the residual rows, which pair into X F_{(2k+1)(n+1)}(X−2) h_t(X)
   with monic quotients h_t of degree t; a row reduction at the residue class, including the boundary shifts m = k and
   m = k+1, makes the matrix block triangular.
5. A truncated multiplication determinant evaluates the remaining block as ((2k+1)(n+1))^m, and the parity of the
   reversal gives the sign (−1)^{kn+binom(k,2)}.

## Falsifier

The identity would fail if the remainder rows at the residue class did not factor through F_{(2k+1)(n+1)}(X−2), or if
the boundary rows for m = k and m = k+1 were not retained by the row reduction.

## Evidence

The proof seat and an independent referee implementation evaluated the original determinants exactly for k ≤ 6, every
0 ≤ m ≤ k+1 and n ≤ 4 (matrices up to order 58), and checked each intermediate reduction on the same range.

## Triage

`theorem`; the statement is Conjecture 11 of arXiv:2308.07642v2, quantified over every k ≥ 1, 0 ≤ m ≤ k+1 and n ≥ 0.

- Proved (formalized): Conjecture 11 for every k ≥ 1, 0 ≤ m ≤ k+1 and n ≥ 0.
- Proved (paper): the closed form gives T_{k,m+1}(n) = (2k+1)(n+1) T_{k,m}(n) for the unsigned determinants, the
  recurrence observed in the source.
- Open: the shifts m outside 0 ≤ m ≤ k+1, and the even powers r = 2k, for which the source reports no closed form.

## ASSUMED-UNVERIFIED
