---
bibkey: hausmann2026weightedmaxcut
authors: Will Hausmann
year: 2026
title: "Weighted Max Cut in Subcubic Graphs"
doi: null
url: https://arxiv.org/html/2611.05178v1
claim: "Question 5.4 asks for an independent side and residual component order at most three in every subcubic graph of odd girth exactly five."
strata_touched:
  - D5/S3/Combinatorics/Graph/ComponentPacking/HausmannQuestion54Refutation
license: CC-BY-4.0
triage: anchor
---

# Independent-side partitions at odd girth five

<!-- GID: D5/L/Certificates/hausmann2026weightedmaxcut -->

## Verified locator

- Primary HTML: https://arxiv.org/html/2611.05178v1
- Source scope: Section 1 definitions of finite simple graphs, subcubic degree
  and odd girth; Section 5, Question 5.4.

Hausmann, *Weighted Max Cut in Subcubic Graphs*, arXiv:2611.05178v1,
Section 1 and Question 5.4 in Section 5, fixes finite simple graphs,
subcubic degree at most three, and odd girth as the shortest odd cycle length.
Question 5.4 reads:

> Does every subcubic graph G of odd girth exactly five admit a partition
> V(G)=L∪R such that L is independent and every component of G[R] has order
> at most three?

The formal claim quantifies over every finite vertex presentation and simple
graph, without a size cutoff. It retains both partition conditions,
independence, and the order bound for every actual induced connected component.
The odd-girth predicate requires a simple five-cycle and excludes every
shorter odd simple cycle. Decidable finite presentations add no mathematical
restriction.

The repository refutation uses the explicitly labelled GP(7,2). Its exact
edge list and the deductive finite decision tree belong to the Lean source;
the source paper is the supplier of the question, not of this refutation.
The proof establishes a connected set of four residual vertices for every
independent side. It asserts neither a size-minimal counterexample nor priority.

Lemma 4.7 supplies a residual-order-six statement. Theorem 2.2 is a weighted-cut
mechanism under a component-union bipartiteness condition. Neither supplies
an order-three partition. The source states that an affirmative answer to
Question 5.4 would imply a weighted 4/5 bound in its odd-girth class; the
refutation of that sufficient structural route does not refute that bound.
Questions 5.3 and 5.5 are separate.

The inspected primary HTML has SHA-256
`49bc3e301c8bea370cc9e9114b211a64ef529a70d268016c6e41d83254abe2d3`.
The quoted question and these locators establish source correspondence,
not worldwide openness or a novelty claim.
