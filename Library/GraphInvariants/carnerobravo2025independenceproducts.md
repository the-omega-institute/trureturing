---
bibkey: carnerobravo2025independenceproducts
authors: Andrés Carnero Bravo
year: 2025
title: On independence complexes of graph products
doi: null
url: https://arxiv.org/abs/2505.06457v2
claim: "Theorem 21 gives a suspended independence-complex conclusion for induced subgraphs of lexicographic products; Question 22 asks for unsuspended membership in the hereditary class W."
strata_touched:
  - D5/S3/Geometry/FiniteGraphVertexSubstitution
license: citation-only
triage: anchor
---

# Independence complexes of lexicographic products

Primary: Andrés Carnero Bravo, *On independence complexes of graph products*,
arXiv:2505.06457v2, 11 November 2025.

## Source scope

Section 2 defines the independence complex $I(G)$ and the lexicographic
product $G\circ H$: vertices are pairs, with adjacency either over an edge
of $G$ or within a single fiber over an edge of $H$.
The paragraph immediately preceding Proposition 7 defines:

- $\mathcal P$: $I(G)$ is contractible, homotopy equivalent to a wedge of
  spheres, or homotopy equivalent to a disjoint union of wedges of spheres.
- $\mathcal{SP}$: $I(G)$ is contractible or homotopy equivalent to a wedge
  of spheres.
- $\mathcal W$: every induced subgraph has property $\mathcal P$.
- $\mathcal{SW}$: every induced subgraph has property $\mathcal{SP}$.

Section 4, in the proof of Theorem 19, writes the independence complex of
an induced subgraph of $G\circ H$ as a polyhedral join over an induced
subgraph of $G$, with factors the independence complexes of induced
subgraphs of $H$.

Theorem 21 states that, for $G,H\in\mathcal{SW}$ both of order at least two
and every induced subgraph $F$ of $G\circ H$, the suspension $\Sigma I(F)$
is contractible or homotopy equivalent to a wedge of spheres.
Question 22 asks, under those same hypotheses, whether
$G\circ H\in\mathcal W$. Thus its requested conclusion concerns the
unsuspended complexes of all induced subgraphs; Theorem 21 does not supply
that conclusion.

## Verified locator

- URL: https://arxiv.org/abs/2505.06457v2
- Version v2, Section 2 (the definitions of $I(G)$, $G\circ H$, and
  $\mathcal P$, $\mathcal{SP}$, $\mathcal W$, $\mathcal{SW}$), and the
  paragraph immediately preceding Proposition 7.
- Theorem 21 and Question 22.

## Local realization refinement

`FiniteGraphVertexSubstitution.oneVertexReplacementEquiv` is a local
finite-coordinate construction in this setting, not a theorem attributed
to this paper. Its base graph and current fibers are arbitrary finite
types, the fibers may carry different graphs, and only the selected old
fiber is required to be a singleton. A chosen vertex in the new fiber
provides the basepoint. The result is a homotopy equivalence from the
actual new substitution independence realization to the actual quotient
wedge of the old realization and the simplicial link-join realization.
Other fibers may be empty, and the restricted link complex may have no
faces; the pure-right singleton still supplies the join basepoint.

The paper's simplicial-complex convention includes the empty face; the
local coordinate realizations use nonempty faces. In particular, an
ordinary topological join interpretation requires nonempty factor
realizations and is not asserted in the empty-link case. The exact
heterogeneous telescope, coordinate maps and quotient topology are local
proof content. This bridge supplies neither the hereditary sphere-wedge
conclusion of Question 22 nor a novelty claim; the full question remains
open in this delivery.
