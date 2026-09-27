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

## Prior exact refutation and attribution

The distinct [prior-refutation Library note](demonstrandum2026pandeyrefutation.md)
provides the structured source for the local result; this note remains
the source for Pandey's graph definition and conjecture.

The public note [*Refutation of the Parity Conjecture for Independence
Polynomials of Generalized Petersen Graphs (arXiv:2601.03293, Conjecture 4.1)*](https://github.com/demonstrandum-research/artifacts/blob/94db9ed50d48a57aae5ccb72e6a95a2b8f8f39d3/problems/p2-factory/kills/pandey-parity/WRITEUP.md)
in `demonstrandum-research/artifacts` already gives a complete refutation
of this exact conjecture. Its immutable commit is
`94db9ed50d48a57aae5ccb72e6a95a2b8f8f39d3`, with provider-reported author
and committer timestamp `2026-06-13T01:23:03Z`; the exact file blob is
`a82a8fe898b3ecb7dc94608f32cb2cf97ce4cc1e`. The note's internal June 11
date is unverified and is not used as its public provenance date.
The source bytes have SHA-256
`2c5af094fda2424c95bd47ca3ef2cfba7dbbcfd4a74039ae963c367769881fe1`.

Section 3(c) explicitly gives `GP(3,1)` and its real-rooted polynomial
`1+6x+6x^2`, the same counterexample used by the local theorem. Section
3(d) also gives the isomorphism `GP(7,2) -> GP(7,3)`:
`u_j -> v'_(3j mod 7)`, `v_j -> u'_(3j mod 7)`. Multiplication by 3 is
invertible modulo 7, so this map is a bijection. Outer edges map to
step-3 inner edges, step-2 inner edges map to outer edges with step
`6 = -1 mod 7`, and spokes map to spokes. Both parameter pairs satisfy
Definition 2.1. Isomorphic graphs have the same independent-set counts
and hence the same polynomial, but 2 and 3 have opposite parity. The
universal biconditional therefore gives contradictory predictions.
This explicit argument alone refutes the full biconditional; it does
not require either graph's roots to be computed. The note's additional
enumeration, Sturm, checker, and audit claims are not verification
evidence adopted here.

This prior exact resolution supersedes the bounded no-hit literature
screen for [issue 8619](https://github.com/the-omega-institute/trureturing/issues/8619).
The historical `open-problem-resolution` novelty-admission basis was
invalid because the exact assertion had already been publicly refuted.
It is not eligible as a newly solved open problem. The conservative
`proof_shape: bind-only` assessment remains; no replacement admission
basis or escape witness is asserted. The valid frozen mathematics is
retained under CLAUDE §§1.3 and 3.2. The repository contribution is its
Lean formalization of a known refutation. The typed `Refuted` binding
records that local theorem under spec §11.20.5, without claiming
worldwide novelty. This Library note attributes the graph and conjecture
to Pandey and the prior explicit refutation to the public note above.
