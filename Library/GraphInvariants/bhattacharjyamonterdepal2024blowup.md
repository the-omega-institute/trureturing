---
bibkey: bhattacharjyamonterdepal2024blowup
authors: Bikash Bhattacharjya, Hermie Monterde, Hiranmoy Pal
year: 2024
title: "Quantum walks on blow-up graphs"
doi: 10.1088/1751-8121/ad6653
url: https://arxiv.org/abs/2308.13887v2
claim: "Conjecture 1 excludes PGST between twin copies of every vertex divisible by 2^(t-1) in the double blow-up of P_(2^t*r-1), for t >= 2 and an odd prime r; P_11 at source vertex 4 refutes it."
strata_touched:
  - D5/S3/Quantum/Dynamics/PathDoubleBlowUpPGSTRefutation
license: citation-only
triage: anchor
---

# Quantum walks on blow-up graphs

## Verified locator

DOI: https://doi.org/10.1088/1751-8121/ad6653

Source: https://arxiv.org/abs/2308.13887v2

The locators refer to the arXiv v2 manuscript's printed page numbers:
Section 1, pages 1–2 (PGST and U(t)); Section 2, page 2 (blow-up);
Section 3, page 3 (transition matrix, equation (3)); Section 5, page 5
(Theorem 3); Section 8, page 8 (P_11 argument and Conjecture 1);
Section 12, page 13 (the question asking whether Conjecture 1 is true).

## Definitions and criterion

Section 1, pages 1–2 states:

> A graph G exhibits PGST between u and v if there is a sequence τ_k ∈ ℝ such that lim_{k→∞} |U(τ_k)_{u,v}| = 1, i.e., |U(t)_{u,v}|² can be made arbitrarily close to one through appropriate choices of t.

The convention is U(t) = exp(itA). The frozen propagator uses exp(-itA),
so this U(t) is represented by hamiltonianPropagator A (-t).

Section 2, page 2 states :

> The blow-up of G, denoted by ⊎ⁿG, is the graph with vertex set ℤ_n × V, and two vertices (l, u) and (m, v) are adjacent in ⊎ⁿG if and only if the vertices u and v are adjacent in G.

For the double blow-up the copy set is {0, 1}. Path vertices have one-based
labels 1, …, n. The formal index j : Fin n represents label val(j) + 1,
and adjacency is |v − w| = 1.

Theorem 3 in Section 5, page 5 gives equivalent conditions for a vertex
whose eigenvalue support excludes zero: PGST between its twins with phase
−1, simultaneous approximation of every supported eigenvalue phase to
−1, almost periodicity of the original vertex with phase −1, and even
coefficient sum for every integral zero relation on its eigenvalue support.

## Conjecture and refutation

Section 8, page 8, Conjecture 1 states:

> Let n = 2^t r − 1, where t ≥ 2 and r is an odd prime number. If u is a multiple of 2^{t−1}, then PGST does not occur between (0, u) and (1, u) in the double blow-up of P_n.

The module PathDoubleBlowUpPGSTRefutation proves its negation with t = 2,
r = 3, n = 11 and source vertex u = 4. Its vertex-4 support is
±(√6+√2)/2, ±√3, ±1 and ±(√6−√2)/2, each with weight 1/8.
The P_11 argument preceding the conjecture uses θ_5 − θ_9 + θ_11 = 0,
but θ_9 = −√2 has zero weight at this vertex. The arithmetic relation
therefore cannot be applied to its support.

The same obstruction applies at source vertices 2, 6 and 10, whose support
contains the three eigenvalues used in that relation. This is a source
argument, not a further conclusion formalized in the settling module.

Section 12, page 13 asks whether Conjecture 1 is true and, if not, which
parameters admit PGST. The general proposed classification, PGST iff
2^t divides u under the conjecture's assumptions, remains open here.
The source's broad assertion about every even vertex of P_11 and its
use in Remark 1 must be restricted to vertices with the required support;
the general Theorem 3 criterion is compatible with the vertex-4 refutation.
