# Ordered and singular integer H1 of a finite coordinate complex

## Abstract

Ordered and singular integer H1 of a finite coordinate complex.

Let V be a finite linearly ordered vertex type and K a pre-abstract simplicial complex on V. All chains in this comparison have integer coefficients.

**Definition 1.1 (Actual intersection simplices).**

Lean statement: `D5/S3/Geometry/FiniteSimplicialSingularHomology.intersectionSimplexEquiv`

*Formalization.* `D5/S3/Geometry/FiniteSimplicialSingularHomology.intersectionSimplexEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Continuous singular simplices in a positive-coordinate face intersection correspond to small singular simplices carried by every selected star. The maps are the actual subspace inclusion and its pointwise subtype lift, and commute with singular faces.

**Definition 1.2 (Intersection chain identification).**

Lean statement: `D5/S3/Geometry/FiniteSimplicialSingularHomology.columnCoproductIso`

*Formalization.* `D5/S3/Geometry/FiniteSimplicialSingularHomology.columnCoproductIso` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each ordered degree p, the Cech-singular column is isomorphic as a chain complex to the coproduct of actual singular chains of the p-face intersections. The basis maps identify actual continuous simplices. Empty intersections have no generators.

**Theorem 1.3 (Coefficient-sum comparison).**

Lean statement: `D5/S3/Geometry/FiniteSimplicialSingularHomology.columnAugmentation_isIso`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplicialSingularHomology.columnAugmentation_isIso` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair p,q of natural numbers, the actual coefficient-sum augmentation of column p induces a degree-q homology isomorphism. The proof combines the explicit chain identification, intersection contractions, and preservation of finite coproducts by homology.

**Definition 1.4 (The exact degree-one comparison).**

Lean statement: `D5/S3/Geometry/FiniteSimplicialSingularHomology.orderedH1IsoSingular`

*Formalization.* `D5/S3/Geometry/FiniteSimplicialSingularHomology.orderedH1IsoSingular` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every V and K above, homology of the ordered triangle-to-edge-to-vertex short complex is isomorphic to Mathlib singular homology in degree one of TopCat.of of the subtype FiniteConeCollapse.realization K, with coefficient object ModuleCat.of Z Z. The actual coefficient-sum and small-chain augmentations give the two total comparisons. No good-cover or homology-isomorphism premise is assumed. Empty realizations and ghost vertices are included.

## References

- Truth anchor: `D5/S3/Geometry/FiniteSimplicialSingularHomology.columnAugmentation_isIso`
- Truth anchor: `D5/S3/Geometry/FiniteSimplicialSingularHomology.columnCoproductIso`
- Truth anchor: `D5/S3/Geometry/FiniteSimplicialSingularHomology.intersectionSimplexEquiv`
- Truth anchor: `D5/S3/Geometry/FiniteSimplicialSingularHomology.orderedH1IsoSingular`
- Dependency: [D5/S3/Geometry/FiniteSimplicialOpenCover](FiniteSimplicialOpenCover.md)
- Dependency: [D5/S3/Geometry/SimplicialPersistence/OrderedChains](SimplicialPersistence/OrderedChains.md)
- Dependency: [D5/S3/Topology/TauCeti/AlgebraicTopology/Singular/OrderedCech](../Topology/TauCeti/AlgebraicTopology/Singular/OrderedCech.md)
