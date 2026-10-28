# Finite component models and vertex wedges

## Abstract

Finite coordinate sphere bouquets, disjoint components, and selected-vertex wedge closure.

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

For finite pre-abstract simplicial complexes K,L satisfying WPlus, and any existing selected vertices a,b, construct SelectedVertexWedgeClosure K L a ha b hb. Normalize the input vertices using the two actual native singleton-cylinder retractions, replace both arms by their based packets, and rearrange the quotient into the selected concatenated bouquet and every unselected component. The component count is m+n-1. Finally use based_inverse only between native finite realizations to obtain both relative inverse homotopies at actual vertices. No cylinder retraction on an arbitrary quotient is assumed. This is a classical finite wedge closure ingredient for Carnero Bravo, arXiv:2505.06457v2, Question 22. Complete finite-component join closure, arbitrary-index reduction, and the graph-substitution conclusion are separate obligations and are not asserted here.

## References

- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure.SelectedVertexWedgeClosure`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure.WPlus`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure.bouquetComplex`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure.bouquetQuotientHomeomorph`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure.normalComplex`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure.normalHomeomorph`
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
