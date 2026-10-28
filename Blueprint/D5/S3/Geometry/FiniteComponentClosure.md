# Finite component models, vertex wedges, and joins

## Abstract

Finite coordinate sphere bouquets, disjoint components, selected-vertex wedges, and complete finite-component joins.

**Definition 1.1 (Native finite sphere models).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure.sphereComplex`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure.sphereComplex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The zero-dimensional sphere is the complex of two distinct vertices. Higher sphere complexes are iterated simplicial joins with this two-point complex. Ghost ambient vertices are permitted; no unproved singleton face is added.

**Definition 1.2 (Actual Euclidean spheres).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure.sphereHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure.sphereHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural dimension d, the coordinate realization of sphereComplex d is homeomorphic to the standard unit sphere in Euclidean space of dimension d+1. The base case is the explicit two-point homeomorphism; the induction uses the actual simplicial-join realization homeomorphism and the existing Euclidean sphere-join homeomorphism.

**Definition 1.3 (Finite positive-sphere bouquets).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure.bouquetComplex`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure.bouquetComplex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A BouquetSpec is a finite list of positive sphere dimensions, counted with repetitions. Each native sphere is embedded with its selected vertex identified with one common coordinate vertex. The empty list is a single actual vertex and therefore one point component.

**Definition 1.4 (The actual bouquet quotient).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure.bouquetQuotientHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure.bouquetQuotientHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The disjoint union of the finite sphere family and a separate common point, with precisely the repeated sphere basepoints and common point collapsed, is homeomorphic to the coordinate bouquet. The quotient kernel and surjectivity include the empty family.

**Definition 1.5 (Standard sphere quotient presentation).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure.standardBouquetHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure.standardBouquetHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The native finite bouquet is homeomorphic to the actual quotient bouquet of standard Euclidean spheres. Each sphere homeomorphism transports its specified basepoint, so this is an identification of actual quotient spaces.

**Definition 1.6 (All finite components).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure.normalComplex`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure.normalComplex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The normal model is the tagged disjoint union of m coordinate bouquets. Different empty lists give different point components; no point component is deleted.

**Definition 1.7 (The tagged coproduct homeomorphism).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure.normalHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure.normalHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate realization of the normal complex is homeomorphic to the sigma type of its bouquet realizations, with their coproduct topology. The canonical normalPoint is the common vertex of the selected tagged bouquet.

**Definition 1.8 (Nonempty finite component homotopy types).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure.WPlus`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure.WPlus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

WPlus K means that the realization of K is homotopy equivalent to a normalComplex with a positive finite component count and a finite positive-sphere list for each component. Lists may be empty. This definition does not assert an arbitrary-index reduction.

**Definition 1.9 (Exactly the selected components merge).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure.selectedWedgeSpec`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure.selectedWedgeSpec` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For input counts m,n and selected indices i,j, the output has m+n-1 indices. It enumerates one bouquet with list p(i) concatenated with q(j), every p(k) with k different from i, and every q(l) with l different from j. The finite enumeration retains repetitions and empty lists.

**Definition 1.10 (The actual vertex gluing).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure.vertexWedgeComplex`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure.vertexWedgeComplex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ambient vertex set is the quotient of the tagged input vertex sets identifying exactly the two selected vertices. The face collection is the union of the mapped input face collections. Its realization is homeomorphic to the actual topological quotient wedge.

**Definition 1.11 (Full based closure data).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure.SelectedVertexWedgeClosure`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure.SelectedVertexWedgeClosure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The data contain positive input model counts, their bouquet specifications and selected indices, a separate BasedEquivalence from each original selected vertex to its model vertex, the based quotient-wedge normalization, an output component index, a direct WPlus witness, and a BasedEquivalence from the actual glued native vertex to that output normal vertex. BasedEquivalence contains continuous forward and backward maps, both strict basepoint equations, and both inverse homotopies relative to the corresponding singleton.

**Definition 1.12 (Selected-vertex WPlus wedge closure).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure.selectedVertexWedgeClosure`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure.selectedVertexWedgeClosure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For finite pre-abstract simplicial complexes K,L satisfying WPlus, and any existing selected vertices a,b, construct SelectedVertexWedgeClosure K L a ha b hb. Normalize the input vertices using the two actual native singleton-cylinder retractions, replace both arms by their based packets, and rearrange the quotient into the selected concatenated bouquet and every unselected component. The component count is m+n-1. Finally use based_inverse only between native finite realizations to obtain both relative inverse homotopies at actual vertices. No cylinder retraction on an arbitrary quotient is assumed. This is a classical finite wedge closure ingredient for Carnero Bravo, arXiv:2505.06457v2, Question 22. The cone-rebasing construction keeps the quotient map unchanged and changes its inverse by a native vertex-to-apex based equivalence. Its exact forward homotopy trace lies in the collapsed cone; composing the quotient with that trace is constant, which makes both concatenated inverse homotopies relative to the chosen vertex. Two such cone collapses on one native union yield the based auxiliary base-quotient splitting without assuming a quotient cylinder retraction. The selected-vertex wedge result is independent of the finite-component join result below. Arbitrary-index reduction and the graph-substitution conclusion are separate obligations and are not asserted here.

**Definition 1.13 (Every join term and multiplicity).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure.finiteJoinSpec`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure.finiteJoinSpec` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For positive component counts m,n, the dimension list concatenates the p+q+1 terms over every pair of components and every occurrence of a sphere in their lists; n-1 copies of each left p+1 suspension term; m-1 copies of each right q+1 suspension term; and (m-1)(n-1) copies of dimension one. Empty lists are actual point components and remain in the component count. Sphere occurrences and repeated dimensions retain their multiplicities. The all-point case m=n=2 therefore produces one circle.

**Definition 1.14 (Both carriers and all relative homotopies).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure.FiniteComponentJoinClosure`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure.FiniteComponentJoinClosure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The closure data contain the positive input component counts and finite lists, their actual normalizing homotopy equivalences, the actual native join equivalence to the single output bouquet specified by finiteJoinSpec, and the actual ordinary quotient join equivalence. At every source native vertex, the data include continuous maps and inverses, both strict basepoint equations, and both inverse homotopies relative to the source and target singleton. The ordinary join receives the same full based packet at the inverse image of that vertex under the simplicial-join realization homeomorphism. A direct WPlus witness is also retained.

**Definition 1.15 (Complete finite-component WPlus join closure).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure.finiteComponentJoinClosure`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure.finiteComponentJoinClosure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For finite pre-abstract simplicial complexes K,L satisfying WPlus, construct FiniteComponentJoinClosure K L. A cone collapse is rebased at a native cone vertex while preserving its original quotient map: the exact native homotopy trace remains in the collapsed cone, so both inverse homotopies fix the chosen point. Two such collapses on one native union give the based auxiliary split. The cone modulo its base is identified by an actual homeomorphism with a native suspension, with its base class mapped to the actual north-pole vertex. Iterating the two-component split contributes one suspension per extra component; decomposing the suspension of a disconnected input contributes the circle terms. Native common-vertex distribution normalizes bouquet joins, using the existing actual Euclidean sphere-join homeomorphism for every natural pair of dimensions, including S0. The empty bouquet remains a point and its join is contracted as an actual cone. Reindexing through finite dimension fibers preserves every sphere occurrence and puts the output in the four-block order of finiteJoinSpec. Every further basepoint adjustment uses native finite vertex cylinders or an already constructed native based presentation. No quotient HEP or arbitrary quotient cylinder is assumed. This is the finite closure ingredient of Carnero Bravo, arXiv:2505.06457v2, Question 22, and does not prove the full graph-substitution question.

**Definition 1.16 (Empty whole left factor).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure.ordinaryJoinEmptyLeft`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure.ordinaryJoinEmptyLeft` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary topological spaces X,Y, IsEmpty X produces an elimination map from the actual ordinary join quotient of X and Y to the empty type. This branch concerns an empty whole factor, separately from a nonempty point bouquet or the augmented simplicial join convention.

**Definition 1.17 (Empty whole right factor).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure.ordinaryJoinEmptyRight`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure.ordinaryJoinEmptyRight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary topological spaces X,Y, IsEmpty Y produces an elimination map from the actual ordinary join quotient of X and Y to the empty type. No point is inserted into an empty ordinary join.

## References

- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure.FiniteComponentJoinClosure`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure.SelectedVertexWedgeClosure`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure.WPlus`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure.bouquetComplex`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure.bouquetQuotientHomeomorph`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure.finiteComponentJoinClosure`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure.finiteJoinSpec`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure.normalComplex`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure.normalHomeomorph`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure.ordinaryJoinEmptyLeft`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure.ordinaryJoinEmptyRight`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure.selectedVertexWedgeClosure`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure.selectedWedgeSpec`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure.sphereComplex`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure.sphereHomeomorph`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure.standardBouquetHomeomorph`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure.vertexWedgeComplex`
- Dependency: [D5/S3/Geometry/EuclideanSphereJoin](EuclideanSphereJoin.md)
- Dependency: [D5/S3/Geometry/FiniteConeUnionWedge](FiniteConeUnionWedge.md)
- Dependency: [D5/S3/Geometry/FiniteVertexCylinder](FiniteVertexCylinder.md)
- Dependency: [D5/S3/Geometry/SingletonRetractionBasedInverse](SingletonRetractionBasedInverse.md)
