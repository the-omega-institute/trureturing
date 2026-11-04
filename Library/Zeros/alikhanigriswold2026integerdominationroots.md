---
bibkey: alikhanigriswold2026integerdominationroots
authors: Saeid Alikhani; Max Griswold
year: 2026
title: On the Integer Domination Root Conjecture
doi: 10.48550/arXiv.2608.00109
url: https://arxiv.org/abs/2608.00109v1
claim: Section 4 item 2 asks whether order 33 is minimal for a connected ordinary domination root minus four; item 3 asks whether infinitely many connected finite simple graphs have that root.
strata_touched:
  - D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly
  - D5/S3/Combinatorics/Graph/Domination/AlikhaniGriswoldMinOrderRefutation
license: citation-only
triage: anchor
---

# On the Integer Domination Root Conjecture

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2608.00109
- Version: https://arxiv.org/abs/2608.00109v1
- Theorem 2.1 gives the finite base; Section 4 item 2 (printed page 5) is the minimum-order question; item 3 is the infinite-family question.

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

## Minimum-order question

Section 4 item 2 asks:

> Is n=33 the minimal order of a graph admitting -4 as a domination root?

The positive assertion includes both a connected graph of order 33 with
D(G,-4)=0 and the exclusion of every connected graph of positive order
below 33. The source's finite simple undirected connected-graph convention
and ordinary dominating-subset count apply to both clauses.

AlikhaniGriswoldMinOrderRefutation.result negates that complete assertion.
Its connected 21-vertex, 25-edge graph has ordinary domination evaluation
zero at -4, contradicting the exclusion clause. The proof uses the existing
MinusFourReassembly.zero_of_messages directly with the same graph,
decomposition and exact message pairs (-1024,972) and (-3328,6912).
The corresponding dossier is
[the minimum-order question](../../Problems/alikhani-griswold-2026-minus-four-minimum-order.md).

This result does not prove that 21 is minimal. The published G33
attainment and the separate Section 4 item-3 unbounded-family result remain
distinct prior conclusions. The source attribution and citation-only
license boundary above apply equally to item 2; the bounded source screen
does not establish worldwide priority or exhaustive nonresolution.
