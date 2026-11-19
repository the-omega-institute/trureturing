---
bibkey: choi2026healing
authors: Jeehoon Choi, Suhwan Yoo, Chaeyeon Kim, Hee Young Kwon, Changyeon Won
year: 2026
title: "Coordination three heals, coordination four is hard: the antiferromagnetic Potts model with a costly third state"
doi: 10.48550/arXiv.2610.41277
url: https://arxiv.org/html/2610.41277v1
claim: "The constructive procedure (Proposition 15, Corollary 16) needed at most three chain stages in all our tests; is the chain length bounded by a constant?"
strata_touched:
  - D5/S3/Combinatorics/Graph/Potts/HealingUnbounded
license: citation-only
triage: anchor
---

# Frustration and the healing question

## Verified locator

DOI: [10.48550/arXiv.2610.41277](https://doi.org/10.48550/arXiv.2610.41277).
Source: [arXiv:2610.41277v1](https://arxiv.org/html/2610.41277v1),
Section VIII, Open problems, item (1); Appendix B, Preliminaries,
Lemmas 11–14, Constructive version, Proposition 15 and Corollary 16.

Appendix B defines the frustration of a graph as the minimum number of
monochromatic edges of a two-colouring. For a vertex set X, let
φ(X)=|X|+fr(G−X), using the induced graph on the remaining vertices.
An independent set is tight when φ(X)=fr(G). A tight set is augmentable
when adjoining one new vertex leaves it independent and tight; otherwise
it is stuck.

Proposition 15 concerns a connected graph other than K₄ of maximum degree
at most three, a stuck tight set S, and fr(G−S)≥1. It bounds the number
of chain stages by the number of components of G−S. Section VIII asks
whether an absolute constant could replace this input-dependent bound.

The formal assertion in HealingUnbounded asks for a uniform constant C
bounding |S∖T| for some augmentable tight T with |T|=|S|. A uniform
stage bound would imply such a displacement bound: the current chain set
after j exchanges differs from S by at most j deletions, and each tested
single exchange adds at most one further deletion. Thus refuting the
displacement assertion also refutes a uniform stage bound, independently
of whether stages are numbered starting at zero or one.

The triangle-tree construction and its displacement lower bound are
repository deductions; the source supplies the definitions and question,
not that counterexample. No global literature-priority assertion is made.
