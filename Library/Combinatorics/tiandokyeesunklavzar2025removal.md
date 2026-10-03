---
bibkey: tiandokyeesunklavzar2025removal
authors: Jing Tian; Pakanun Dokyeesun; Sandi Klavzar
year: 2025
title: "On the variety of general position problems under vertex and edge removal"
doi: 10.48550/arXiv.2510.01294
url: https://arxiv.org/html/2510.01294v2
claim: "Conjecture 3.4 asserts gp_o(G-x) <= gp_o(G) + deg_G(x) whenever x is not a cut vertex of a simple connected graph G."
strata_touched:
  - D5/S3/Combinatorics/Graph/TianDokyeesunKlavzarOuterGeneralPositionRefutation
license: citation-only
triage: anchor
---

# Outer general position under vertex removal

## Locator

DOI: 10.48550/arXiv.2510.01294

URL: https://arxiv.org/html/2510.01294v2

The assertion is Conjecture 3.4 in section 3.2 of the accessed arXiv v2.
Section 2 considers simple connected graphs. Section 1 defines two vertices
as Z-positionable when every shortest path between them has no internal
vertex in Z. An outer general position set Z requires this for two endpoints
in Z and for one endpoint in Z and the other outside Z. The outer general
position number is the largest cardinality of such a set.

Conjecture 3.4 states:

> If x is not a cut vertex of a graph G, then
> gp_o(G-x) <= gp_o(G) + deg_G(x).

The finite formal statement quantifies over every finite vertex type and
every native simple connected graph. Vertex removal is induced deletion.
Non-cut means that deletion does not increase the component count. This
includes the convention that deleting the sole vertex of K1 leaves the
empty graph with zero components; the empty outer number is zero.
These endpoint conventions complete the formal statement and are not
additional quotations from the paper.

## Counterexample and scope

Take a cycle of length twelve. Replace two opposite vertices by independent
sets A and B of four vertices each, preserving their two cycle neighbors.
Call the resulting 18-vertex graph H. Add x adjacent to the neighbor of A
in one cycle direction and the neighbor of B in the same direction, producing
G on 19 vertices. Then H is the actual induced deletion G-x, both graphs
are connected, and x has degree two.

The eight vertices in A union B form an outer general position set in H.
In G, a five-color assignment puts every outer general position set in
at most five colors with no color repeated: each distinct same-color pair
has a selected endpoint and a shortest path containing the other vertex
internally. Thus gp_o(G-x) >= 8 and gp_o(G) <= 5, contradicting 8 <= 5+2.
The distance certificates refer to the actual edge lists and native graph
walks, rather than assumed distance data.

The source's simplicial-vertex bound in Proposition 3.5 and conditional
lower bound in Theorem 3.3 are separate statements. This counterexample
has two nonadjacent neighbors and does not settle those statements.

## Source boundary

The author-linked v2 PDF and the arXiv v2 PDF have the same SHA-256:
`642fcda6fa53788475acad3dbc8232df3928be28707ec30093d370c46bf8db70`.
The author's publication page reports Last modified 2026-09-17.
The later survey arXiv:2501.19385v5, revised 2026-08-16, cites the journal
publication and summarizes removal results without settling this
degree-dependent conjecture in the accessed summary.

No exact settlement was identified in the accessible checked scope,
including the versioned source, the author-linked PDF and the later survey.
This bounded evidence qualifies the named arXiv v2 problem for the
version-specific open-problem-resolution route; it does not establish
worldwide non-settlement. Inaccessible bodies are outside that checked
scope. A prior exact settlement would disqualify this route.

The later journal DOI 10.1016/j.dam.2026.02.044 identifies a publication
whose body has not been read here. Its conjecture numbering, wording,
and settlement status are unverified. This note attributes definitions
and the displayed conjecture only to the accessed arXiv v2. It makes no
claim of novelty, publication priority, or complete literature clearance.
