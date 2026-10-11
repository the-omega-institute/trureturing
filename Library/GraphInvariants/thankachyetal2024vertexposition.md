---
bibkey: thankachyetal2024vertexposition
authors: M. Thankachy, E. J. Thomas, U. Chandran, J. Tuite, G. Di Stefano, G. Erskine
year: 2024
title: "On the Vertex Position Number of Graphs"
doi: 10.7151/dmgt.2491
url: https://arxiv.org/abs/2209.00359v2
claim: "Problem 2.4: Is the ratio vp(G)/vp⁻(G) bounded for connected graphs?"
strata_touched:
  - D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation
license: citation-only
triage: anchor
---

# Vertex position numbers

## Verified locator

DOI: 10.7151/dmgt.2491

Source: https://arxiv.org/abs/2209.00359v2

Discussiones Mathematicae Graph Theory 44 (2024), 1169–1188.
The locators below use the arXiv v2 PDF pagination.

## Definition 2.1

Page 3: “For any graph $G$ and a fixed vertex $x \in V(G)$, a set
$S_x\subseteq V(G)$ is an $x$-position set if for any $y\in S_x$ no vertex of
$S_x\setminus \{ y\}$ lies on any $x,y$-geodesic in $G$.”

Page 3: “The $x$-position number of $G$ is defined to be the maximum
cardinality of an $x$-position set and is denoted by $p_x(G)$ or simply $p_x$.”

Page 3: “The maximum value of $p_x(G)$ among all vertices $x$ of $G$ is
called the upper vertex position number $\mathrm{vp}(G)$ (or simply the
vertex position number) of $G$.”

Pages 3–4: “Similarly, the minimum value of $p_x(G)$ among all vertices of
$G$ is called the minimum vertex position number $\mathrm{vp}^-(G)$ of $G$.”

A geodesic includes its endpoints. Thus $\{x\}$ is an $x$-position set,
but a connected graph has no $x$-position set of size at least two containing
$x$. The Lean predicates retain this convention, quantify over every shortest
walk and take the finite supremum over every subset of the vertex carrier.

## Problem 2.4

Page 5: “Is the ratio $\frac{\mathrm{vp}(G)}{\mathrm{vp}^-(G)}$ bounded for
connected graphs?”

Lemma 2.3, page 5, gives a family $G(r)$ for $r\ge 3$ with
$\mathrm{vp}^-(G(r))=r$ and $\mathrm{vp}(G(r))=6r-4$.
Its ratios approach six. This is a family of examples, not a universal upper
bound. The authors' survey, “General position problems in graphs”,
[arXiv:2501.19385v5](https://arxiv.org/abs/2501.19385v5), lists the boundedness
question among its open problems.

## Refutation mechanism

The Lean result constructs connected graphs $G_m$ for every $m\ge 2$.
From one hub every shortest ray contributes at most one vertex to a position
set, giving an upper bound $2m+1$. From another vertex, $m(m-1)$ vertices
lie on one sphere and hence form a position set. The resulting lower bound
$m(m-1)/(2m+1)$ on the ratio is unbounded.
The source's separately stated degree, eccentricity and graph-class bounds
retain their stated scopes; no replacement universal upper bound is asserted.
