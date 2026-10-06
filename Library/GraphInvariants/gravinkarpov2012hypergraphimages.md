---
bibkey: gravinkarpov2012hypergraphimages
authors: "N. V. Gravin; D. V. Karpov"
year: 2012
title: "On proper colorings of hypergraphs"
doi: 10.1007/s10958-012-0884-2
url: https://arxiv.org/abs/1111.1558v1
claim: "Indexed graph images and clique-edge rerouting provide a published antecedent for representative-pair exchange arguments."
strata_touched:
  - D5/S3/Combinatorics/Graph/BipartiteSubgraphDensity
license: citation-only
triage: anchor
---

# Hypergraph images and clique-edge rerouting

Published in *Journal of Mathematical Sciences* 184(5) (2012),
pages 595–600. The [preprint](https://arxiv.org/pdf/1111.1558v1)
contains the graph-image definition in Section 2 and the image
transformation in Section 3, in the proof of Theorem 1(2).

Definition 3 assigns one graph edge to each owning hyperedge, with
both endpoints contained in that hyperedge. The assignment is a
bijection of indexed edges; parallel graph edges remain distinct
when they represent different hyperedges.

For a hypergraph with maximum vertex incidence degree Delta and
minimum hyperedge size delta, put k=ceil(2 Delta/delta). Theorem 1
gives a proper vertex coloring with k+1 colors. When delta is at
least three and k is at least three, it gives k colors. Proper
hypergraph coloring here means that no hyperedge is monochromatic.

The proof first obtains a graph image with maximum degree at most k.
For a clique component, it replaces an edge uw owned by a hyperedge
e with uv, where v is another vertex of e. An auxiliary directed
graph records how these replacements connect components, and the
proof constructs the required coloring.

## Relation to hereditary sparse pair selections

The owner-preserving reroute is an existing published method. The
repository's pair-selection problem instead assumes that every legal
selection satisfies an indexed edge bound on every induced vertex
set. It minimizes the number of four-cliques and concludes that
each owner on a remaining four-clique has exactly two available
vertices. Supports of size two are allowed.

These are different hypotheses and conclusions. Hereditary average
degree does not itself bound maximum vertex degree, and Theorem 1(2)
does not include the mixed-rank rigidity conclusion. The paper is
therefore an antecedent and reusable source of method, not a direct
substitute for that exact theorem. This comparison makes no claim
that the repository statement is original or absent from all other
literature or formal libraries.

The bibliographic metadata and preprint statement were checked against
the original source. No source text or code is vendored, and this note
does not claim a Lean implementation of the paper's coloring theorem.
