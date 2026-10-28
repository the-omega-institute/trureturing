---
bibkey: demo2026periodicity
authors: Gregory Demo, David Lund, Oleksiy Al-saadi
year: 2026
title: "On the Periodicity of k-distance Graphs"
doi: null
url: https://arxiv.org/abs/2606.25493v1
claim: "Conjecture 1: Any connected graph G=(V,E) has rho^2(G) <= |V|-3. Preliminaries and Definition 1 specify exact-distance iteration and the least positive return up to graph isomorphism, with zero when no return exists."
strata_touched:
  - D5/S3/Combinatorics/Graph/Walks/DemoStrongPeriodBoundRefutation
license: citation-only
triage: anchor
---

# Strong periodicity under the exact-distance operator

## Source and locators

The fixed source is [arXiv:2606.25493v1](https://arxiv.org/abs/2606.25493v1),
[original PDF](https://arxiv.org/pdf/2606.25493v1) and
[original HTML](https://arxiv.org/html/2606.25493v1).
The complete twelve-page PDF and HTML were inspected in the source qualification;
the definitions and conjecture agree between them.

Preliminaries define the k-distance operator on simple undirected graphs: retain the
vertex set and join two vertices exactly when their geodesic distance is k.
Unreachable pairs do not give edges. The operator can produce disconnected graphs.
The notation G_t^k means t-1 applications, with G_1^k = G.

Definition 1 minimizes over indices f > 1 for which G_f^k is isomorphic to G_1^k;
the strong period rho^k(G) is f-1. If no such f exists, its value is zero.
The separate weak period requires label preservation and is not the strong period.

Section 4, Conjecture 1, printed PDF page 11,
[HTML locator](https://arxiv.org/html/2606.25493v1#Thmconjecture1):

> Any connected graph G=(V,E) has rho^2(G) <= |V|-3.

The graph-order conditions on cycle lemmas and the hypotheses of the ear and
existence results are local. The complete source qualification found no global
order lower bound, singleton exclusion or requirement of period greater than one.
A nearby argument calls an edgeless graph disconnected without distinguishing
the singleton; it supplies no stated global convention excluding that graph.
The authors' intended corrected range is unverified.

## Exact mathematical scope

The formal claim ranges over finite vertex types and simple connected graphs,
without a nontriviality or positive-edge condition. Its operator is defined even
on disconnected iterates. It minimizes positive iteration counts t up to ordinary
graph isomorphism, with source index f=t+1, and returns zero when no return exists.
Cardinality and period are cast to the integers before subtracting three.

For the connected singleton, the exact-distance-two graph is itself, the first
permitted return is t=1, and the period is one. The asserted bound becomes
1 <= -2. This refutes the full printed universal claim under these definitions;
it does not settle a version restricted to larger graph orders.

The singleton fixed-point fact is already recorded in
[Erickson et al., arXiv:2409.02306v1](https://arxiv.org/abs/2409.02306v1),
Theorem 4.1 and the proof of Theorem 6.5; its source note is
[erickson2024metamour](erickson2024metamour.md).
It supplies no independent novelty for this result. Standard shortest-distance,
identity-isomorphism, iteration, least-witness and cardinality facts are reused
from pinned Mathlib; no source conjecture is assumed as an axiom.

## Bounded qualification

The source qualification inspected the original v1 source and metadata, the
earlier metamour paper, and Zelinka's *A note on periodicity of the 2-distance
operator*, Discussiones Mathematicae Graph Theory 20(2) (2000), 267-269,
DOI 10.7151/dmgt.1125. Bounded title, identifier, author, correction,
metamour and singleton-period searches found no published correction or
refutation of this exact bound in the successfully inspected sources.
Blocked or rate-limited search endpoints supply no negative evidence.
This does not certify absence of private, unpublished or unsearched resolutions,
and makes no worldwide novelty claim. The full-bound refutation is derived in
the repository; the cited paper states the conjecture rather than its refutation.
