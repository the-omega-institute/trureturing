---
bibkey: mosqueraloistanaka2026stablecategory
authors: David Mosquera-Lois and Kohei Tanaka
year: 2026
title: Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces
doi: 10.48550/arXiv.2609.39615
url: https://arxiv.org/abs/2609.39615v1
claim: Question 6.3 asks whether the stable category of every finite T₀-space is at most twice its weak category.
strata_touched:
  - D5/S3/Topology/MatchedFaceIncidenceForest
  - D5/S3/Topology/DescendingClosureContiguity
  - D5/S3/Topology/RelativeDerivedContiguity
  - D5/S3/Topology/BarycentricGraphDistance
  - D5/S3/Topology/BarycentricNeighborhoodIteration
  - D5/S3/Topology/BarycentricBaseRigidity
license: citation-only
triage: anchor
---

<!-- GID: D5/L/Topology/mosqueraloistanaka2026stablecategory -->

# Weak and stable category of finite spaces

Question 6.3 asks whether `cat_s(X) ≤ 2 cat_w(X)`.
The stable invariant takes the minimum of the ordinary finite-space category
over all barycentric subdivisions. The weak invariant is the category of
the realization of the order complex. The paper uses unreduced category.

## Locator

Section 2 and Question 6.3 of the cited preprint give the category invariants
and the proposed inequality. DOI 10.48550/arXiv.2609.39615.
[Preprint v1](https://arxiv.org/abs/2609.39615v1)

## A coface bound on a collapse sequence

If each lower face paired with a triangle has at most two original
triangular cofaces, a collapse sequence removing all triangles has
an edge–triangle incidence forest on its deleted faces. The analogous
proof works in any fixed pair of consecutive dimensions. The Lean theorem
extracts an indexed matching from an actual elementary collapse sequence.
An additional coface must precede the assigned one. A cycle would have
a greatest rank with two distinct predecessors.

For a two-dimensional collapse onto a tree, color the vertices of the
first barycentric subdivision according to whether the face survives
the triangle removals. The induced complexes are the subdivided tree
and the incidence forest. The corresponding neighborhoods in the
second barycentric subdivision retract by intersecting each face with
the selected vertices. Each forest component contracts in the connected
ambient complex, giving a two-piece categorical cover. The Lean
incidence result addresses the forest step.
[Subdivision and contiguity](https://arxiv.org/abs/1605.01322v2)

## Contiguity under subdivision

`DescendingClosureContiguity` proves finite ranked interpolation of
pointwise ordered order maps, relative to all vertices on which they agree.
For face posets, intersection with a selected vertex set gives the
descending map on its meeting-face neighborhood. The module proves the
relative contiguity chain for this map, the cover of flags by two such
neighborhoods, and preservation of contiguity classes by the induced
face-image maps.

`RelativeDerivedContiguity` constructs a complex whose simplices consist
of old base vertices and a flag of outside faces containing those old
vertices. For a finite source vertex type, full bases, and a contiguous
pair of vertex maps preserving and reflecting base membership, it proves
that the induced maps are joined by a simplicial contiguity chain on the
relative derived complexes. The common union of outside-face images
allows the exterior maps to be interpolated while the old map is fixed,
and permits one contiguous change of the old base map between those
interpolations. The retained base is full and every step respects the
base and exterior vertex sets, so the construction can be iterated.

`BarycentricGraphDistance` proves exact doubling of the extended
one-skeleton distance between two subcomplexes under ordinary
barycentric subdivision. The proof contracts alternating face walks
by choosing a vertex at each inclusion minimum. It also shows that
a full subcomplex containing a graph neighborhood of radius `D`
contains the corresponding neighborhood of radius `2D` after subdivision.
`BarycentricNeighborhoodIteration` constructs the order complex
in the same simplicial representation and proves the neighborhood
bound at every depth.

`BarycentricBaseRigidity` uses two applications of the neighborhood
bound to rule out a first move in a same-depth contiguity chain. If
the only vertex that can be adjoined to every incident maximal base
face is the original base vertex itself, that vertex remains fixed
throughout the chain. For relative cones each maximal base face has
its own exterior tip. Applied to a nontrivial strong core, this
obstructs a categorical piece containing the whole subdivided base.

This distance calculation supports a quantitative obstruction to
a uniform subdivision depth. Relative subdivisions of cones over a
twice subdivided triangulated torus can have arbitrarily long
prescribed initial stretches of constant category, with that
category equal to one more than the torus dimension. The Lean
modules verify the subdivision and distance ingredients. The cone
construction is a separate mathematical proof, and Question 6.3 on
the eventual stable category remains open.
