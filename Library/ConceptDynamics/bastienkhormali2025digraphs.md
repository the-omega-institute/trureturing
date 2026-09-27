---
bibkey: bastienkhormali2025digraphs
authors: Alexander Bastien and Omid Khormali
year: 2025
title: On Link-irregular Digraphs
doi: null
url: https://arxiv.org/abs/2512.20494v1
claim: Conjecture 6 states that a link-irregular tournament exists on n vertices if and only if n is at least 6; the paper proves the assertion through order 8 and reports computational verification through order 100.
strata_touched:
  - D5/S3/ConceptDynamics/GraphIrregularity/LinkIrregularTournamentExistence
license: citation-only
triage: anchor
---

<!-- GID: D5/L/ConceptDynamics/bastienkhormali2025digraphs -->

# Link-irregular digraphs

The paper defines the directed link of a vertex `v` in a digraph `D` as the
subdigraph induced on the union of the out-neighbors and in-neighbors of `v`.
A digraph is link-irregular when the directed links at every two distinct
vertices are non-isomorphic. Conjecture 6 states that a link-irregular
tournament exists on `n` vertices if and only if `n >= 6`.

The source proves the conjecture for `n <= 8`. Its order-six tournament has
the following one-based arcs:

`(1,6), (1,3), (1,4), (2,1), (3,2), (3,4), (3,6), (4,5), (4,6),
(4,2), (5,1), (5,2), (5,3), (5,6), (6,2)`.

The paper also reports computational verification through order 100. It does
not contain a proof for all orders. The repository theorem uses the displayed
order-six tournament and a symbolic construction for every order at least
seven; it does not rely on the reported search.

## Verified locator

- arXiv abstract and version record: https://arxiv.org/abs/2512.20494v1
- Source HTML: https://arxiv.org/html/2512.20494v1
