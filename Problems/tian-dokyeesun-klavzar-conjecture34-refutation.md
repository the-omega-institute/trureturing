---
slug: tian-dokyeesun-klavzar-conjecture34-refutation
bibkey: tiandokyeesunklavzar2025removal
doi: 10.48550/arXiv.2510.01294
url: https://arxiv.org/html/2510.01294v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/TianDokyeesunKlavzarOuterGeneralPositionRefutation.result
---

# Tian–Dokyeesun–Klavžar Conjecture 3.4 refutation

## Problem

Conjecture 3.4 in section 3.2 of arXiv:2510.01294v2 states:

> If x is not a cut vertex of a graph G, then
> gp_o(G-x) <= gp_o(G) + deg_G(x).

The formal claim ranges over all finite simple connected graphs and every
non-cut vertex. Deletion is the actual induced graph on vertices other
than x. Non-cut means that deletion does not increase the number of
connected components. This retains K1, with empty deletion, zero empty
outer number, and singleton outer number one.

A pair is Z-positionable when every shortest path between its endpoints
has no internal vertex in Z. An outer general position set requires this
for every pair with at least one endpoint in Z. The outer number is the
maximum cardinality among all such subsets.

## Motivation

The theorem
`D5/S3/Combinatorics/Graph/TianDokyeesunKlavzarOuterGeneralPositionRefutation.result`
negates the complete finite assertion. The counterexample has 19 vertices,
an actual non-cut vertex of degree two, deletion outer number at least
eight, and original outer number at most five.

## Gap

A replacement general upper bound is not determined. The local proof does
not establish universal formulas for the outer numbers of a parameterized
family, or the source's separate simplicial-vertex and conditional lower
bounds.

## Route

Begin with a cycle of length twelve. Replace two opposite vertices by
independent sets A and B of four vertices, preserving their cycle neighbors.
This graph H has 18 vertices. Add x adjacent to one neighbor of A and the
corresponding neighbor of B in the same cycle direction. The new graph G
has 19 vertices, and H is isomorphic to the actual induced deletion G-x.

Exact finite certificates construct walks descending the proposed distance
by one at each adjacent step and bound every walk below by that distance.
Consequently the two distance tables are the native graph distances.
The shortest-path condition is equivalent to excluding every geodesic
triple with distinct selected endpoint and selected internal vertex.

The eight vertices in A union B satisfy this condition in H. Mapping walks
in both directions through the deletion isomorphism transfers native
distances and the eight-vertex set to G-x. For G, five colors suffice for
an obstruction assignment: every distinct same-color pair admits a shortest
path with one selected endpoint and the other vertex internally.
Every outer set is therefore injectively colored, so it has size at most
five. Both graphs are connected and x has degree two. The proposed bound
would imply 8 <= 5+2.

## Falsifier

An incorrect edge, failed distance certificate, missing same-color
obstruction, failure of the induced-deletion isomorphism, or mismatch
between the formal shortest-path predicate and the source definition
would invalidate the argument. A restriction in a later source would
limit attribution to that source, without changing the accessed v2 claim.

## Evidence

The frozen module defines induced deletion, the component-count
non-cut predicate, all-shortest-path outer position, its finite maximum,
and the full closed claim. Its sole public theorem is `result : Not claim`.
All certificate and transfer facts are local to that proof. The axiom
closure is `propext`, `Classical.choice`, and `Quot.sound`.

## Triage

The finite universal bound is refuted by the formal result. This is a
Tier 1 external named conjecture preregistered in issue 12543. The version-specific
admission basis is `open-problem-resolution`; the proof shape is `content`,
with the public refutation produced by the local graph certificate and
walk-construction chain. Its computational use is `certified-instance`
with the exact `refutes` relation from `result` to `claim`.

Qualification is confined to Conjecture 3.4 in section 3.2 of
arXiv:2510.01294v2. The author-linked v2 PDF and the arXiv v2 PDF
have the same SHA-256:
`642fcda6fa53788475acad3dbc8232df3928be28707ec30093d370c46bf8db70`.
The author's publication page reports Last modified 2026-09-17.
The later survey arXiv:2501.19385v5, revised 2026-08-16, cites the
journal publication and summarizes removal results without settling this
degree-dependent conjecture in the accessed summary. No exact settlement
was identified in the accessible checked scope. Inaccessible bodies are
outside that scope. This bounded qualification is not a worldwide absence
or priority claim; a prior exact settlement would disqualify this route.

### What the settlement shows

Proved in the frozen module: for this witness, adding x supplies a short
route between the two replacement classes. Shortest paths then obstruct
selected pairs in G, while deleting x restores the eight-vertex outer set.
The two-neighbor degree budget therefore fails to bound the increase.

Source-attested neighboring statements, not settled by this module:
Theorem 3.3 is a conditional lower bound and Proposition 3.5 concerns
simplicial vertices. Here x has two nonadjacent neighbors and is not
simplicial. This witness does not refute either separate statement. It
supplies no verdict on other source results or questions; dependencies
on the false bound require separate examination.

Open: a corrected general upper bound, sufficient structural restrictions,
and any parameterized extension. The result does not prove general
formulas for a family of graphs.

## ASSUMED-UNVERIFIED

The body of the later journal publication, DOI 10.1016/j.dam.2026.02.044,
has not been read here. Its wording, numbering and settlement status are
unverified. Attribution and qualification are confined to the accessed
arXiv v2. Novelty, exhaustive literature completeness and publication
priority are unverified. The frozen refutation is
`D5/S3/Combinatorics/Graph/TianDokyeesunKlavzarOuterGeneralPositionRefutation.result`,
with result statement identity
`sha256:cbf825b91d7bb0631ec60152fd9cd48a3ac8267ec06d6014075741f7e5ffac71`.
