---
bibkey: shapiro2026spectrum
authors: Boris Shapiro
year: 2026
title: The (n−2,2)-Spectrum of a Graph
doi: null
url: https://arxiv.org/abs/2605.17501v2
claim: The unweighted fourth-moment inversion question asks whether Laplacian and cubic data recover the four-edge support-forest counts.
strata_touched:
  - D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroQuarticInversionRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: null. Crossref's title query returned no matching work.
Source: https://arxiv.org/abs/2605.17501v2

Section 6, page 4, equations (6.1) and (6.2), defines the character and
edge-word expansion of the trace moment. Section 6.1, page 5, defines
support-subgraph counts:

> For a finite simple graph H without isolated vertices, let N_H(G) denote the number of edge subsets S ⊆ E(G) for which the graph with edge set S and vertex set formed by the endpoints of S is isomorphic to H. No inducedness condition is imposed on the ambient graph G.

The cycle-count convention in Section 6, page 4, is:

> If σ ∈ Sₙ, let c₁(σ) be the number of fixed points of σ and let c₂(σ) be the number of two-cycles in its cycle decomposition.

The edge transposition is defined there by:

> Let τ_e = (ij) denote the transposition corresponding to an edge e = ij.

Section 9, page 11, discusses degree-by-degree inversion after adjoining
Laplacian spectral data and distinguishes recovery from all moments.
Section 12, page 13, Outlook item 1 states:

> Compute an explicit closed formula for the unweighted fourth moment and invert it, modulo Laplacian and cubic data, on the finite list of four-edge support forests. The degree-three inversion is complete by the cubic inversion theorem above.

## Scope

The inversion implication compares trees of the same order, with equal
Laplacian characteristic polynomials, equal support counts through three
edges, and equal moments of orders two, three and four. The counterexample
has unequal five-vertex path counts. This answers the inversion part of
item 1; it does not preclude an explicit fourth-moment formula. The
all-moment separation statements remain distinct questions.
