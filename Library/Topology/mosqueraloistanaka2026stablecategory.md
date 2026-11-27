---
bibkey: mosqueraloistanaka2026stablecategory
authors: David Mosquera-Lois and Kohei Tanaka
year: 2026
title: Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces
doi: 10.48550/arXiv.2609.39615
url: https://arxiv.org/abs/2609.39615v1
claim: Question 6.3 asks whether the stable category of every finite T₀-space is at most twice its weak category.
strata_touched:
  - D5/S3/Topology/RelativeConeRigidity
  - D5/S3/Topology/MatchedFaceIncidenceForest
  - D5/S3/Topology/DescendingClosureContiguity
  - D5/S3/Topology/SubdivisionCategoricalCover
  - D5/S3/Topology/SmallPosetSubdivisionCategory
  - D5/S3/Topology/FiniteCategoricalCoverCertificate
  - D5/S3/Topology/SmallAcyclicCategoricalCovers
  - D5/S3/Topology/RelativeDerivedContiguity
  - D5/S3/Topology/BarycentricGraphDistance
  - D5/S3/Topology/BarycentricNeighborhoodIteration
  - D5/S3/Topology/BarycentricBaseRigidity
  - D5/S3/Topology/ConnectedCategoryGraft
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
and the proposed inequality. Proposition 5.2 and Question 6.2 give the
height-one family and the connected realization problem. DOI
10.48550/arXiv.2609.39615.
[Preprint v1](https://arxiv.org/abs/2609.39615v1)

## Connected realizations

For a connected finite poset `X`, identify a minimal point with one of the
minima of the height-one poset `B_m` with `m ≥ 2` common maxima. The graft has
ordinary category `max(cat(X), m)`. The Lean theorem gives the exact criterion
for a categorical lower cover of each size. The principal lower sets of `B_m`
contract to the shared point while fixing it. In the lower bound, a piece
containing two maxima would contract the four-point retract whose identity is
isolated among pointwise-comparable maps.

Subdivision preserves this union and its minimal shared point. At positive
depth the subdivided `B_m` has a lower cover by the face posets of two
subdivided tree stars. Leaf pruning gives the rooted contraction required at
the common point. The same cover argument at positive depths yields stable
category `max(cat_s(X), 2)`. The classical wedge formula gives weak category
`max(cat_w(X), 2)`.

For `a ≥ 2`, take the opposite face poset of the first barycentric subdivision
of a triangulated `(a − 1)`-torus. For each face dimension, the open set of
faces meeting that dimension color contracts through the projection onto its
discrete color class. The torus cup-length gives weak category `a`, so all
three categories equal `a`. Grafting `B_c` yields every connected triple
`(a, a, c)` with `2 ≤ a ≤ c`. The Lean module proves the ordinary cover formula
used in this construction. The stable and weak formulas and the torus argument
are mathematical deductions using the subdivision and classical category
comparisons.

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

## Conjecture 6.1 and categorical covers

Conjecture 6.1 asks for the least size of a finite space with both category
inequalities strict. Corollary 4.2 attains twelve points. The Lean theorem
`SubdivisionCategoricalCover.hasCategoricalCover_double_subdivision`
supplies the subdivision step for the lower bound. Two categorical induced
subposets covering a finite poset give two categorical open subsets of its
second subdivision. In the first subdivision each chain meeting a chosen
set contracts through its intersection with that set. In the second
subdivision the smallest chain in each flag makes the two lower sets cover.

The computer-assisted lower bound is twelve. For a connected core of at
most eleven points, simultaneous strictness with weak category at least two
requires at least four maximal points. The corresponding Lean theorem
partitions such a core into two categorical subsets and bounds the category
of its second subdivision by two. It uses the two extrema above and below
each intermediate point in a core and the limit of four intermediate points
when there are at least three minima.

With weak category one, the nine-point theorem of Cianci and Ottina reduces
the remaining range to sizes nine through eleven. A core with at most two
maxima already has a two-cover by principal lower sets. For the rest, take
the McKay catalogue of Hasse diagrams on eight, nine and ten points and
extend each poset at one maximum. Use a lower ideal with no greatest
element, exclude all old maxima, and for each old up beat point include that
point and exclude its former least strict upper neighbor. Discard orders
with a down beat point, and use connectedness and vanishing reduced
homology over the field of two elements. The latter conditions hold for
every weakly contractible candidate. This yields 2, 10 and 93 isomorphism
classes with at least three maxima. The Lean kernel checks two explicit
lower sets and their inclusion-to-constant zigzags for every listed class.
The exhaustive enumeration uses the published catalogue and integer
computation.

Passing to cores preserves the three categories, which are additive over
components. Any component with a strict weak-to-stable inequality needs at
least nine points. For weak category one this uses Cianci and Ottina. For
weak category at least two, a core on at most eight points has a stable
two-cover by the same intermediate-point argument. Under the size bound
of eleven the other components therefore contribute equally to all three
categories.
[Conjecture 6.1 and Corollary 4.2](https://arxiv.org/html/2609.39615v1#S6)
[McKay catalogue](https://users.cecs.anu.edu.au/~bdm/data/digraphs.html)

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

## Rigidity for relative cones

After any positive number of derived subdivisions fixing the base of a
cone, every retained maximal base face has one strict coface and a
distinct exterior tip. A further relative step sends each unique coface
to the new tip indexed by that coface, so this incidence persists.

Suppose the maximal faces through each original base vertex intersect
in that vertex and at least two such faces meet there. The distinct tips
exclude exterior vertices from the intersection of their coface
neighborhoods. The maximal-face criterion then fixes every original base
vertex through all same-depth contiguity chains of the base inclusion.
The Lean theorem holds at every subsequent ordinary subdivision depth.
Question 6.3 also requires deciding the existence of a categorical
two-cover, whose members may meet only parts of the base.
