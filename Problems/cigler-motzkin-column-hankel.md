---
slug: cigler-motzkin-column-hankel
bibkey: cigler2022motzkin
doi: 10.48550/arXiv.2204.09910
url: https://arxiv.org/abs/2204.09910v4
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumn.result
---

# Reduced Denominators for Hankel Determinants of Motzkin-Triangle Columns

## Problem

Johann Cigler, *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin
paths*, arXiv:2204.09910v4, Section 1, Conjecture 1.3, equation (1.30). M_{n,k}(t) is the weighted number of Motzkin
paths from (0,0) to (n,k) that never go below the axis, with up and down steps of weight 1 and horizontal steps of
weight t; d_m^{(k)}(n,t) = det(M_{m+i+j,k}(t))_{0≤i,j<n} and D_m^{(k)}(x,t) = Σ_n d_m^{(k)}(n,t) xⁿ. With
e = (−1)^{binom(k+1,2)}, A_{k,0} = 1 − e x^{k+1} and A_{k,r} = 1 − e L_r(t) x^{k+1} + x^{2(k+1)} for r > 0 (equation
(1.28)), the conjecture states

D_m^{(k)}(x,t) = r_m^{(k)}(x,t) / ∏_{j=0}^{⌊m/2⌋} A_{k,(k+1)(m−2j)}(x,t)^{1+j(m−j)},

with deg_x r_m^{(k)} = binom(m+1,3) + k (binom(m,1) + binom(m,2) + binom(m,3)).

## Motivation

The theorem `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumn.result` establishes the identity for every column
k ≥ 0 and every m ≥ 1 over ℤ[t], with the exact x-degree of the numerator.

## Gap

Pre-registration issue 12625 records the literature screen: Krattenthaler's Corollary 9 gives the weaker denominator
for k = 0 (the paper's Theorem 1.1); Cigler–Krattenthaler and Chern–Shi, arXiv:2608.27208, evaluate shifts m ≤ 2 and
two residue classes for m ≤ k + 1, not the reduced exponents and numerator degree in general. This is a bounded
negative finding.

## Route

1. Specializing the boundary weight s to t in the proof of Conjecture 2.1 of the same paper
   (`CiglerMotzkinHankel`), a Christoffel-type formula writes d_m^{(k)}(n,t) as a determinant with k fixed
   Chebyshev nodes and m confluent zero nodes, with sign (−1)^{binom(k+1,2)}.
2. The two Binet branches and same-branch Vandermonde cancellation bound the polynomial parts by j(m − j), so the
   sequence satisfies the linear recurrence whose characteristic polynomial is the reversed denominator, with the
   x^{k+1} structure.
3. Negative-index determinants fix the exact x-degree of the numerator.

## Falsifier

The statement would fail if the fixed nodes changed the sign e or the exponents, or if the first nonzero
negative-index determinant vanished for some k.

## Evidence

An independent referee implementation checked the identity symbolically in t for k ≤ 3, m ≤ 4 and for several
integer t for k ≤ 4, m ≤ 5.

## Triage

`theorem`; the statement is Conjecture 1.3 of arXiv:2204.09910v4, quantified over every k ≥ 0 and m ≥ 1.

- Proved (formalized): the reduced denominator and the exact numerator degree for every column k and every m ≥ 1.
- Proved (paper): Conjecture 1.2 of the same paper follows, since binom(m,j) ≥ 1 + j(m − j) makes the denominator of
  Conjecture 1.3 divide that of Conjecture 1.2.
- Open: whether the exponents 1 + j(m − j) are the reduced ones, i.e. whether the numerator is coprime to the
  denominator.

## ASSUMED-UNVERIFIED

The literature screen is limited to the arXiv records named above, web and GitHub searches and the repository checks.
