---
bibkey: hongwuxia2026sensitivity
authors: Zhen-Mu Hong, Zi-Yi Wu, Zheng-Jiang Xia
year: 2026
title: "Graph Sensitivity of Cartesian Products with Matched Bridges"
doi: 10.48550/arXiv.2610.09483
url: https://arxiv.org/html/2610.09483v1
claim: "Section 7, Problem 2 asks whether f_2(Q_9) is 3 or 4."
strata_touched:
  - D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSupport
  - D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeComponent
license: citation-only
triage: anchor
---

# A structural anchor in hypercube sensitivity

## Verified locator

DOI: 10.48550/arXiv.2610.09483

Versioned URL: https://arxiv.org/html/2610.09483v1

Exact locator: Section 7, Problem 2,
https://arxiv.org/html/2610.09483v1#Thmproblem2 .
The versioned primary HTML, dated 7 October 2026, was read on
15 November 2026.

## Definition and open target

The source defines `f_t(G)` as the minimum maximum degree of an induced
subgraph on `alpha(G)+t` vertices, where `alpha` is the independence number.
Problem 2 begins:

> Determine whether f₂(Q₉)=3 or 4.

For the Boolean nine-cube, `alpha(Q_9)=256`, so a positive answer at three
requires 258 actual cube vertices inducing maximum degree at most three.
A proof of the alternative four must exclude every such support.
The problem also asks for improvements in other finite-factor cases;
those broader questions are not claims of this module.

## Relation of the construction to the source

The grid-wedge construction is a repository derivation motivated by this
problem, not a result attributed to Hong, Wu and Xia. It constructs a
uniform family of connected regular induced subgraphs in square-dimensional
cubes. Its case `d=3` has 72 vertices and degree three. It does not provide
a 258-vertex witness, exclude every 258-vertex candidate, or settle Problem 2.

The construction uses an explicit signing with parity of occupied earlier
coordinates. Pinned `Archive.Sensitivity` orders the Boolean basis so its
recursive Huang matrix instead uses parity of unoccupied earlier
coordinates. On an edge in direction `k`, the two signs differ by `(-1)^k`.
The vertex potential `(-1)^(sum of occupied coordinate indices)` supplies
the corresponding diagonal switching. This convention correspondence is a
mathematical explanation, not a claim that a Lean matrix bridge has been
checked merely by compiling the combinatorial construction.

## Literature limits

The general equality mechanism is prior work. Laplante, Naserasr, Sunny
and Wang, *Sensitivity conjecture and signed hypercubes*,
https://hal.science/hal-04080411/document , discuss regularity and switching
to all-positive signs after Lemma 4.1 (PDF page 9, printed page 7), and
Theorem 6.2 gives a regular induced subgraph on the equality-degree
vertices (PDF page 26, printed page 24). The final journal DOI is
10.1145/3777401; its full text was not available in this search.
Karasev, https://arxiv.org/abs/1907.11175v2 , Sections 1.2--1.3, and
Mathews, https://arxiv.org/abs/1907.12357v2 , Sections 2.2--2.3, provide
exterior-algebra and Clifford formulations. Those methods and the general
equality principles are not claimed as new here.

The source https://arxiv.org/abs/2312.15336v1 , Section 1 and
Construction 1, identifies the standard Gray graph as the Levi graph of
the 27-point, 27-line three-dimensional grid. A 72-vertex support is
therefore different from that standard graph. This does not exclude
identity with every generalized Gray construction; Bouwer's 1972
original paper was not read in this search.

On 15 November 2026 the official abstract page listed only v1, and a
bounded Semantic Scholar lookup for the exact source reported zero
citations. Those observations do not exhaust later work or establish
worldwide novelty. Neither uniqueness of the solution nor priority of the
grid-wedge family is claimed. The related texts read in this bounded search
did not exhibit this exact two-layer block family; the candidate new content
is its explicit support, exact size and connectedness.
