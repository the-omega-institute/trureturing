---
bibkey: debruijnerdos1951colour
authors: N. G. de Bruijn and P. Erdos
year: 1951
title: "A Colour Problem for Infinite Graphs and a Problem in the Theory of Relations"
doi: 10.1016/S1385-7258(51)50053-7
url: https://doi.org/10.1016/S1385-7258(51)50053-7
claim: "For a fixed finite number of colors, an infinite graph is colorable when every finite subgraph is colorable; the repository combines this classical result with a separate Cantor counterexample for an infinite palette."
strata_touched:
  - D5/S3/Combinatorics/Graph/ColoringCompactnessBoundary
license: citation-only
triage: anchor
---

# A colour problem for infinite graphs

## Verified locator

- N. G. de Bruijn and P. Erdos, *A Colour Problem for Infinite Graphs and a
  Problem in the Theory of Relations*, Indagationes Mathematicae (Proceedings)
  54 (1951), 371-373.
- DOI: https://doi.org/10.1016/S1385-7258(51)50053-7
- Crossref was queried on 2026-09-23 and matched the title, authors, year,
  journal volume, and pages above.

## Scope

The paper is the literature source for the fixed-finite-palette compactness
theorem: if every finite subgraph of a graph can be colored with a fixed finite
number of colors, then the whole graph can be colored with that many colors.
The formal boundary theorem uses Mathlib's pinned implementation of this result
and only adapts colorings of finite induced subgraphs to its finite-subgraph
premise.

The infinite-palette failure in the repository theorem is not attributed to the
paper. It uses the complete graph on `Set Nat`: each finite induced subgraph can
be injected into `Nat`, whereas a global coloring would inject `Set Nat` into
`Nat`, contrary to Cantor's theorem. The combined sharp-boundary formulation is
therefore assessed as repository-derived while retaining this note as the
source of its classical finite-palette component.
