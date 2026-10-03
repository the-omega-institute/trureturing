---
bibkey: song2026tokenradius
authors: X. Song and C. Dalfó and M. À. Fiol and S. Zhang
year: 2026
title: The Algebraic Connectivity and Laplacian Spectral Radius of Token Graphs
doi: 10.48550/arXiv.2610.00500
url: https://arxiv.org/abs/2610.00500v1
claim: "Conjecture 1.1 asserts that equality of the Laplacian spectral radius of a graph and all its token graphs in the stated range characterizes stars."
strata_touched:
  - D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation
license: citation-only
triage: anchor
---

# The Algebraic Connectivity and Laplacian Spectral Radius of Token Graphs

The Abstract, page 1, defines the token graph:

> For a graph G = (V, E) of order n and an integer k between 1 and ⌊n/2⌋,
> its token graph F_k(G) is the graph whose vertices consist of the
> (n choose k) k-subsets of V, and two vertices of F_k(G) are adjacent
> whenever their symmetric difference is an edge in E.

Section 1, page 4, states:

> Conjecture 1.1. Let G be a graph of order n(≥ 4), the equality
> ρ(F_k(G)) = ρ(G) holds for all k with 2 ≤ k ≤ ⌊n/2⌋ if and only if G ≅ S_n.

Section 2, page 5, fixes the Laplacian and its spectral radius:

> Let L = L(G) = D(G) − A(G) be the Laplacian matrix of G.

> the spectral radius of L is ρ(L) = λ_n. We denote ρ(G) = ρ(L) as the
> Laplacian spectral radius of G.

The eigenvalues are ordered increasingly and are nonnegative. The maximum
of Mathlib's Hermitian eigenvalue family therefore represents the source's
ρ. The star S_n is K_{1,n−1}; the encoding uses Mathlib's star graph on
Fin n centered at zero. Conjecture 1.1 states no connectedness hypothesis.
The graph K₂ ⊔ 2K₁ refutes that literal statement: its two-token graph is
2K₂ ⊔ 2K₁, both Laplacian spectral radii are two, and its edge count is
one instead of the star's three. The conjecture restricted to connected
graphs remains open.

## Source locator

arXiv:2610.00500v1, Abstract (page 1), Conjecture 1.1 (page 4), and
Laplacian notation (section 2, page 5):
https://arxiv.org/pdf/2610.00500v1 .
