---
bibkey: alikhanigriswold2026integerdominationroots
authors: Saeid Alikhani; Max Griswold
year: 2026
title: On the Integer Domination Root Conjecture
doi: 10.48550/arXiv.2608.00109
url: https://arxiv.org/abs/2608.00109v1
claim: Section 4 item 3 asks whether infinitely many connected finite simple graphs have ordinary domination polynomial zero at minus four.
strata_touched:
  - D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly
license: citation-only
triage: anchor
---

# On the Integer Domination Root Conjecture

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2608.00109
- Version: https://arxiv.org/abs/2608.00109v1
- Theorem 2.1 gives the finite base; Section 4 item 3 is the infinite-family question.

## Source and scope

Saeid Alikhani and Max Griswold, arXiv:2608.00109v1, Section 4 item 3:

> Does there exist an infinite family of graphs G satisfying D(G, -4) = 0?

The introduction uses finite simple undirected connected graphs. Ordinary domination
requires every vertex to be selected or adjacent to a selected vertex. Connectedness
is a condition on the graph, not on each dominating subset. Unbounded orders provide
the substantive infinite-family event. The question imposes no fixed cyclomatic
number, degree bound, planarity requirement, or condition on root multiplicity.

Theorem 2.1 reports a 33-vertex, 36-edge graph and a polynomial with a factor x+4.
Its actual edges are independently encoded in MinusFourReassembly.sourceEdges.
Core vertices 0,1,2,3 form a four-cycle. The components outside the core have roots
4,6,8,10,12,18,21,24 and sizes 2,2,2,2,6,3,3,9. Vertex 5 has sole neighbor 4.
The nine-vertex component uses exactly the explicit edges among labels 24 through
32. The branch prose in Section 3.3 does not replace those factual edge data.

The arXiv source uses the perpetual non-exclusive distribution license; a Creative
Commons license is not authenticated. The repository definitions and proofs are
independently written, with attribution for the factual graph and question. No
author code or substantial source prose is reproduced.

The published base and its reported root are existing results. The repository
family construction uses a separate exact restriction/reassembly proof and
small finite component evaluations for the base value. The bounded prior source screen found no
exact later resolution in the checked surfaces; it establishes neither worldwide
novelty nor exhaustive absence of earlier work.
