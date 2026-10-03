---
bibkey: vandre2024marginals
authors: Lina Vandré; Jarn de Jong; Frederik Hahn; Adam Burchardt; Otfried Gühne; Anna Pappa
year: 2024
title: "Distinguishing Graph States by the Properties of Their Marginals"
doi: 10.48550/arXiv.2406.09956
url: https://arxiv.org/abs/2406.09956v2
claim: "Conjecture 16: Given two graphs G and G′ and a condensation set C such that each node in C is connected to at most one node in the neighborhood in V \\ C. If G and G′ are LC-equivalent, it follows that G_c and G′_c are LC-equivalent."
strata_touched:
  - D5/S3/Quantum/Entanglement/GraphCondensationLCRefutation
license: citation-only
triage: anchor
---

# Distinguishing Graph States by the Properties of Their Marginals

L. Vandré, J. de Jong, F. Hahn, A. Burchardt, O. Gühne and A. Pappa,
arXiv:2406.09956, quant-ph; v1 2024-06-14, v2 2025-06-11.
Page numbers below refer to v2.

Conjecture 16, Section V, p. 13:

> Given two graphs G and G′ and a condensation set C such that each node in C is connected to at most one node in the neighborhood in V \ C. If G and G′ are LC-equivalent, it follows that G_c and G′_c are LC-equivalent.

Definition 13, Section V, p. 12:

> Consider a graph G = (V, E) and a set C ⊆ V. The condensed graph G_C = (V_C, E_C) consists of the node set V_C = {c} ∪ (V \ C) and edge set E_C defined in the following way: (i, j) ∈ E_C if either i, j ∈ V \ C and (i, j) ∈ E, or j = c and there exists s ∈ C such that (i, s) ∈ E.

The paper restricts attention to simple connected graphs. Local complementation
(Definition 4, pp. 4–5) complements edges among the neighbours of the selected
vertex and leaves other edges intact. It states on p. 5:

> There is a one-to-one correspondence between the local complementation orbit of a given graph and the orbit under local Clifford operations of the corresponding graph state.

The correspondence is attributed to Van den Nest, Dehaene and De Moor,
Phys. Rev. A 69, 022316 (2004),
https://doi.org/10.1103/PhysRevA.69.022316.

The encoding uses labelled graphs on any finite type, with the at-most-one
outside-neighbour condition imposed on both initial graphs. The fresh vertex
is `none` in `Option {v // v ∉ C}`; outside vertices are `some v`. Adjacency is
exactly Definition 13, symmetrized for undirected graphs.

On vertices 0 through 5, let C = {0, 1, 2}, with initial edges
{01, 02, 05, 14, 23} and final edges {05, 14, 23, 35, 45}.
Both graphs are connected, and each vertex in C has exactly one outside
neighbour. Local complementation at 0, 1, 2, 3, 4, 5 in order maps the first
graph to the second. Their condensed graphs are the star with centre c and
leaves 3, 4, 5, and the diamond with edges {c3, c4, c5, 35, 45}.
The complete graph and the four stars are closed under local complementation;
induction excludes the diamond from the star's LC orbit. Thus the conjecture
fails even with the degree condition imposed on both graphs.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2406.09956
- URL: https://arxiv.org/abs/2406.09956v2
- PDF: https://arxiv.org/pdf/2406.09956v2, Definition 13 on p. 12 and
  Conjecture 16 on p. 13.
