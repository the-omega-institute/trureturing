---
bibkey: rather2026generalposition
authors: B. A. Rather
year: 2026
title: Explicit Formulas and Unimodality Phenomena for General Position Polynomials
doi: 10.48550/arXiv.2603.06930
url: https://arxiv.org/abs/2603.06930v3
claim: "Section 8 item 1 asks for real-rootedness results for general position polynomials; the connected classification is real-rooted if and only if complete."
strata_touched:
  - D5/S3/Combinatorics/Graph/GeneralPosition/RatherRealRootedComplete
license: citation-only
triage: anchor
---

# General position polynomials and real roots

## Verified locator

DOI: 10.48550/arXiv.2603.06930

Source: https://arxiv.org/abs/2603.06930v3

All page numbers refer to the version 3 PDF.

## Definitions

Section 1, page 1:

> All graphs considered are finite, simple and undirected.

Section 2, page 4:

> A subset S ⊆ V(G) is a general position set if there do not exist distinct vertices x, y, z ∈ S such that d(x,z) = d(x,y) + d(y,z)

> For each k ≥ 0, let α_k(G) denote the number of general position sets of size k. The general position polynomial of G is ψ(G) = ∑_{k≥0} α_k(G)x^k.

The finite-subset count is taken once per subset. The formal polynomial lies
in ℤ[X], and its sum stops at the vertex count. General position reuses
`CylinderSevenTen.IsGeneralPosition`, expressed using `SimpleGraph.dist`.
On connected graphs this agrees with shortest-path distance. Real-rootedness
means that every complex zero has zero imaginary part.

## Real-rootedness question

Section 8, item 1, page 29:

> For no nontrivial family is it currently known whether ψ(G) is always real-rooted. Even partial real-rootedness results for chordal graphs, bipartite graphs, or claw-free graphs (in analogy with [8, 13]) would be significant.

For finite nonempty connected simple graphs, the formal theorem proves that
the polynomial is real-rooted exactly when the graph is complete. The proof
uses the first three coefficients, reflection, Vieta's formulas and Newton's
inequality. A full-size general position set excludes any nonadjacent pair
in a connected graph. For a complete graph the polynomial is (1 + X)^n.

The disconnected extension uses a different distance convention and is not
asserted here. The literature screen described in issue #18870 found no
prior connected classification; its completeness is ASSUMED-UNVERIFIED.
