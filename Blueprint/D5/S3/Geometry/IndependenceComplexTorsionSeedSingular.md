# Two-torsion in the actual seed singular homology

## Abstract

Two-torsion in the actual seed singular homology.

**Definition 1.1 (Actual finite bases).**

Lean statement: `D5/S3/Geometry/IndependenceComplexTorsionSeedSingular.edgeFaceEquiv`

*Formalization.* `D5/S3/Geometry/IndependenceComplexTorsionSeedSingular.edgeFaceEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The seed has eleven vertices, thirty-two edges, and twenty-four triangles. Its exhaustive increasing enumerations give bijections to the actual faces of the corresponding cardinalities. The vertex, edge, and triangle bijections identify the free integer groups.

**Definition 1.2 (Both boundary squares).**

Lean statement: `D5/S3/Geometry/IndependenceComplexTorsionSeedSingular.orderedSeedShortComplexIso`

*Formalization.* `D5/S3/Geometry/IndependenceComplexTorsionSeedSingular.orderedSeedShortComplexIso` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The three basis bijections identify the ordered short complex with the original seed integer boundary short complex. Both differential squares use the original signed boundary maps and explicit finite deletion identities.

**Definition 1.3 (The same coordinate realization).**

Lean statement: `D5/S3/Geometry/IndependenceComplexTorsionSeedSingular.seedH1IsoSingular`

*Formalization.* `D5/S3/Geometry/IndependenceComplexTorsionSeedSingular.seedH1IsoSingular` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The seed short-complex homology is isomorphic to Mathlib singular H1 of the actual coordinate realization of seedComplex.toPreAbstractSimplicialComplex with coefficient object ModuleCat.of Z Z. This composes the boundary identification with the generic ordered-to-singular comparison.

**Theorem 1.4 (The transported class has order two).**

Lean statement: `D5/S3/Geometry/IndependenceComplexTorsionSeedSingular.singularSeedClass_nonzero_killed_by_two`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/IndependenceComplexTorsionSeedSingular.singularSeedClass_nonzero_killed_by_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The image of the original seedClass under this isomorphism is nonzero and its natural-number scalar multiple by two is zero. Injectivity transports nonvanishing and linearity transports the annihilation equation. This is a singular seed; the induced king-grid obstruction needed to answer Carnero Bravo Question 32 is a separate conclusion.

## References

- Truth anchor: `D5/S3/Geometry/IndependenceComplexTorsionSeedSingular.edgeFaceEquiv`
- Truth anchor: `D5/S3/Geometry/IndependenceComplexTorsionSeedSingular.orderedSeedShortComplexIso`
- Truth anchor: `D5/S3/Geometry/IndependenceComplexTorsionSeedSingular.seedH1IsoSingular`
- Truth anchor: `D5/S3/Geometry/IndependenceComplexTorsionSeedSingular.singularSeedClass_nonzero_killed_by_two`
- Dependency: [D5/S3/Geometry/FiniteSimplicialSingularHomology](FiniteSimplicialSingularHomology.md)
- Dependency: [D5/S3/Geometry/IndependenceComplexTorsionSeed](IndependenceComplexTorsionSeed.md)
- Dependency: [D5/S3/HomologicalAlgebra/FiniteFreeCoproduct](../HomologicalAlgebra/FiniteFreeCoproduct.md)
