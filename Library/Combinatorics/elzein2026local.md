---
bibkey: elzein2026local
authors: Ayman El Zein, Maidoun Mortada
year: 2026
title: "Impact of local girth on the S-packing coloring of k-saturated subcubic graphs"
doi: 10.48550/arXiv.2603.25113
url: https://arxiv.org/abs/2603.25113v1
claim: "Conjecture 3 states that every 2-saturated subcubic graph is (1,1,2)-packing colorable."
strata_touched:
  - D5/S3/Combinatorics/Graph/ElZeinMortadaSaturatedPackingRefutation
license: citation-only
triage: anchor
---

# El Zein--Mortada saturated subcubic packing conjecture

## Verified locator

DOI: 10.48550/arXiv.2603.25113

URL: https://arxiv.org/abs/2603.25113v1

Version: arXiv:2603.25113v1, submitted 2026-03-26. The title and authors
match the arXiv record. No journal DOI is asserted.

## Statement and definitions

Printed page 27 states:

> Moreover, as we did not find a 2-saturated subcubic graph G such that
> g3(G) >= 4 that is not (1, 1, 2)-packing colorable, we conjecture the
> following.
> Conjecture 3 Every 2-saturated subcubic graph is (1, 1, 2)-packing colorable.

Printed page 2 defines a subcubic graph by maximum degree at most three and
defines k-saturation by requiring every degree-three vertex to have at most k
degree-three neighbours. It defines an S-packing coloring as a partition into
classes whose distinct vertices have graph distance greater than the
corresponding entry of S.

The displayed definition of g3 on printed page 3 uses the maximum of the local
girths of degree-three vertices, while the following prose calls it the
smallest such cycle length. The formal refutation concerns only the printed
Conjecture 3, which contains no local-girth hypothesis, and makes no inference
about which of those readings was intended.

## Counterexample scope

The connected graph with graph6 encoding `FhcYG` has vertices 0 through 6 and
edges 01, 04, 12, 16, 23, 34, 35, 45, and 56. Its degrees are
`[2,3,2,3,3,3,2]`; the degree-three vertices have respectively 0, 2, 2, and 2
degree-three neighbours. The triangle on vertices 3, 4, and 5 forces one of
them into the radius-two color class. Every vertex lies within distance two of
each triangle vertex, leaving a five-cycle after deletion of whichever one is
chosen. The remaining vertices therefore cannot be split into two independent
classes.

The four degree-three vertices have local girths `(5,3,3,3)`. This datum is not
used by the refutation of the unqualified printed conjecture.

## Bounded prior-resolution evidence

The preregistration on issue 8799 records a targeted arXiv and repository
search before the proof probe. It found the source at version 1 and a later
paper resolving other conjectures from the same article, but no resolution of
Conjecture 3 in the searched scope. The current arXiv record still lists only
version 1. Google Scholar and exhaustive non-arXiv literature coverage were not
verified, so no worldwide priority or exhaustive absence claim is made.

The target is a Tier 1 recent named conjecture. The graph, its structural
properties, and its non-colorability are established directly in the formal
module; no novelty is claimed for general packing-coloring methods.
