---
bibkey: browngeorge2025degree
authors: J. I. Brown and I. C. George
year: 2025
title: On the roots of degree polynomials
doi: 10.48550/arXiv.2505.04882
url: https://arxiv.org/abs/2505.04882v1
claim: Conjecture 4.1 asserts that every nonzero degree root z of a graph of order n satisfies |z| ≤ (n − 1)^{|arg(z)/π|}.
strata_touched:
  - D5/S3/Zeros/DegreeRoots/Result
license: citation-only
triage: anchor
---

# Degree polynomial roots

## Verified locator

DOI: 10.48550/arXiv.2505.04882

Source: https://arxiv.org/abs/2505.04882v1

The arXiv title is *The Degree Polynomial*. The published version is
*On the roots of degree polynomials*, Australasian Journal of Combinatorics
92(2), 164–183. Page numbers below refer to that published version.

## Source statements

Section 1, p. 164:

> For any v ∈ V, let deg(v) = deg_G(v) denote its degree in G, and let a_k be the number of vertices of degree k in G. The degree polynomial of G is defined by

\[
D(G;x)=\sum_{v\in V}x^{\deg(v)}=\sum_{k=\delta}^{\Delta}a_kx^k.
\]

Conjecture 4.1, p. 180:

> If z is a nonzero degree root of a graph of order n with argument arg(z) ∈ (−π, π], then |z| ≤ (n − 1)^{|arg(z)/π|}.

## Scope

The Lean definition sums one monomial for each vertex of a simple graph on
`Fin n`, including degree-zero vertices. The conjecture is encoded for
positive n using `Complex.arg`, the complex norm and real powers. The
settling theorem proves the entire encoded inequality. The general
finite-sum estimate permits arbitrary nonnegative real weights and natural
exponents when the constant term is positive and the root norm exceeds one.
Star equality and uniqueness of extremizers are not formalized here.
