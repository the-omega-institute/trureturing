---
bibkey: pandey2026parity
authors: Rohan Pandey
year: 2026
title: "Parity-Dependent Real-Rootedness in Independence Polynomials of Generalized Petersen Graphs"
doi: null
url: https://arxiv.org/abs/2601.03293v1
claim: "Conjecture 4.1 asserts that for all integers n >= 2k+1 the independence polynomial of GP(n,k) has only real roots if and only if k is even, on the graph domain n >= 3 and 1 <= k < n/2."
strata_touched:
  - D5/S3/Combinatorics/GeneralizedPetersen/ParityRefutation
license: citation-only
triage: anchor
---

# Pandey's Parity Conjecture

## Verified locator

URL: https://arxiv.org/abs/2601.03293v1

Version: arXiv:2601.03293v1. The introduction defines the independence
polynomial by counting independent sets. Definition 2.1 gives the graph and
its domain. Conjecture 4.1 (Parity Conjecture), PDF page 4, states:

> For all integers n ≥ 2k+1, the independence polynomial I(GP(n,k),x) has only real roots if and only if k is even.

The TeX source SHA-256 is
`5147f84b91867223e59aa63486af9b4276eadd08dc785fa40ab3c670c80ef004`;
the PDF SHA-256 is
`bae13d4946674f1149b74ef9095d04d9d7ec2d4010dbd8357de52ad88cd066e2`.

## Source semantics

Definition 2.1 permits integer parameters `n >= 3`, `1 <= k < n/2`.
There are vertices `u_i,v_i` for `0 <= i < n`, and undirected edges
`u_i u_(i+1)`, `v_i v_(i+k)`, and `u_i v_i`, with indices modulo `n`.
Over natural parameters this is exactly `3 <= n`, `1 <= k`, `2*k < n`.
The last inequality also expresses the conjecture's `n >= 2k+1`.
No condition `k >= 2` or `n >= 20` occurs in the conjecture or graph
definition. The separate experimental range `20 <= n <= 30` is not a
restriction on the universal conjecture.

The polynomial is the actual independent-set generating polynomial with
integer coefficients, not a transfer-matrix surrogate. The formal result
uses the existing `IndependentPartitionDeletion.independencePolynomial`
and its complex evaluation identity on the full finite vertex set.

## Classical ingredients and scope

`GP(3,1)` is the triangular prism. Its 13 independent sets have cardinality
counts `1,6,6,0,0,0,0`, giving `1+6X+6X^2`. This polynomial is real-rooted
although `k=1` is odd. Neither this polynomial nor the prism's
real-rootedness is claimed as new.

The source cites Maria Chudnovsky and Paul Seymour, *The roots of the
independence polynomial of a clawfree graph*, Journal of Combinatorial
Theory, Series B 97(3), 350–357 (2007). Its theorem also explains the
prism's real-rootedness because the prism is claw-free. This attribution
uses Pandey's citation and the supplied bibliography check; no independent
reading of the original article or unverified DOI is asserted. The Lean
proof instead performs exact counting and real/imaginary-part arithmetic.

## Bounded prior-resolution evidence

The supplied literature screen for preregistration
[issue 8619](https://github.com/the-omega-institute/trureturing/issues/8619)
inspected source v1, the author's public README/code at
https://github.com/Rohan-Pandey1729/polynomial-independence, and exact
identifier, title, author, and public-repository searches. No explicit
resolution of this literal conjecture was located in that bounded scope.
Citation APIs were unavailable and general search engines presented
challenges. This is not an exhaustive absence or worldwide priority claim.
The author's code already compares `GP(n,2)` and `GP(n,3)` by isomorphism
and equal polynomials; no novelty is asserted for those observations.

The target is Tier 1, a recent externally named conjecture. The proposed
admission is `open-problem-resolution`, with conservative
`proof_shape: bind-only` and no escape-witness claim. Any located earlier
resolution of the same literal assertion would defeat that eligibility;
classical knowledge of the ingredients alone is disclosed separately.
