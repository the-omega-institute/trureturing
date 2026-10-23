---
slug: manattu-lakshmanan-2025-cubic-ar-graphs
bibkey: manattu2025radolabeling
doi: 10.48550/arXiv.2502.11760
url: https://arxiv.org/abs/2502.11760v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/EdgeLabeling/CubicARGraph.result
---

## Problem

Manattu and Lakshmanan S., arXiv:2502.11760, Section 7, state: “whether all cubic graphs are AR-graphs is still an open question.” The exact assertion is preregistered in [#14910](https://github.com/the-omega-institute/trureturing/issues/14910).

An injective positive-integer edge labeling makes a vertex additively rigid when all subset sums of its incident edge labels are distinct. An AR-labeling of a graph with $m$ edges is a bijection from the edges onto $\{1,\ldots,m\}$ making every vertex additively rigid. The target includes every finite simple graph of degree three at every vertex, including the empty graph.

## Motivation

The assertion asks whether cubic incidence constraints can always be satisfied while using every label in the shortest possible positive interval. It connects local additive obstructions with the global freedom to permute edge labels.

## Gap

The literature readings supplied with preregistration found only arXiv v1, and the journal version retains the open sentence. The follow-up arXiv:2502.19182 does not settle it. Searches on the title, the authors, “cubic AR-graph” and “AR-labeling” found no settlement in the searched material. The `formal-conjectures` file `ErdosProblems/1.lean` contains no AR statement. These are the supplied search readings rather than a fresh external search or an exhaustive originality claim.

## Route

For three distinct positive labels $a<b<c$, the eight subset sums are distinct exactly when $a+b\ne c$. The degree-sum formula gives $3n=2m$, and every nonempty simple cubic graph has even order at least four.

The orders four and six have explicit labelings. At order four the graph is complete. At order six its complement has degree two and is either two disjoint triangles or a six-cycle, giving the complete bipartite graph or triangular prism. Graph isomorphisms preserve AR-labelings. The complete graph uses labels $01=1,02=2,03=4,12=3,13=5,23=6$. The complete bipartite graph uses the matrix $[[1,2,4],[3,5,6],[7,8,9]]$. For the complement of the cycle $0123450$, the labels are $02=1,04=2,03=4,24=3,25=5,14=6,35=7,13=8,15=9$.

For $m\ge12$, fix two edges meeting at a vertex to labels one and two. There are $(m-2)!$ remaining labelings. The common endpoint contributes $(m-3)!$ bad labelings, its two neighboring endpoints contribute $2(m-3)(m-4)!$ and $2(m-4)(m-4)!$, and each other vertex contributes at most $6T_m(m-5)!$, where

$$T_m=\#\{(a,b):3\le a<b,\ a+b\le m\}=\left\lfloor\frac{(m-5)^2}{4}\right\rfloor.$$

The formula follows by summing the disjoint rows of possible smaller labels. A generic extension lemma counts bijections extending an injection on $j$ specified points by $(k-j)!$. The inequality $4T_m\le(m-5)^2$ and $3n=2m$ show that the sum of bad-event bounds is strictly below $(m-2)!$. The finite union bound therefore leaves a labeling with no bad vertex.

## Falsifier

A finite simple cubic graph whose every bijection onto $\{1,\ldots,m\}$ has an incident pair of labels summing to its third incident label would refute the assertion. A label collision, a missing interval label, or a failure of any event cardinality bound would invalidate the corresponding proposed construction or counting argument.

## Evidence

`D5.S3.Combinatorics.EdgeLabeling.CubicARGraph.result : claim` proves the complete assertion with the exact definitions above. Its helper modules separate the local subset-sum criterion, generic extension count, additive-pair cardinality, marked and free events, finite union bound, small-graph classification, and graph-isomorphism transfer. The exact result and its import dependencies compile through the canonical Lean build entry. The result node in the matching Blueprint Scribe declares a Proved resolution of this problem slug.

## Triage

The counting route produces the label set exactly $\{1,\ldots,m\}$, in addition to excluding the local additive obstruction.

- [open] Whether all $k$-regular simple graphs are AR-graphs for $k\ge4$.

## ASSUMED-UNVERIFIED

No fresh network search was performed because the implementation seat has no network. The literature gap readings are carried from preregistration. The claim concerns finite simple graphs; it imposes neither connectedness nor an additional hypothesis on the labeling interval.
