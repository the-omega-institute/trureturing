# Complex Adjunction

## Abstract

This module supplies the indicated step in the unbounded solidification construction.

The degreewise adjunction uses Mathlib's Functor.mapHomologicalComplexCompIso for categories with zero morphisms and functors preserving zero morphisms. It applies to complexes of any shape and requires no additivity.

**Definition 1.1 (exact Derived Homology Iso).**

Lean statement: `D5/S3/HomologicalAlgebra/Solid/ComplexAdjunction.exactDerivedHomologyIso`

*Formalization.* `D5/S3/HomologicalAlgebra/Solid/ComplexAdjunction.exactDerivedHomologyIso` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact derived functors commute with homology in every integer degree.

**Theorem 1.2 (derived Inclusion postcomp is Right Derived Functor).**

Lean statement: `D5/S3/HomologicalAlgebra/Solid/ComplexAdjunction.derivedInclusion_postcomp_isRightDerivedFunctor`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/Solid/ComplexAdjunction.derivedInclusion_postcomp_isRightDerivedFunctor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact derived inclusion remains a right-derived functor after any postcomposition. This discharges the right-derived composite obligation in `Adjunction.derived`; it requires no existence or adjunction assumption for derived solidification.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/Solid/ComplexAdjunction.derivedInclusion_postcomp_isRightDerivedFunctor`
- Truth anchor: `D5/S3/HomologicalAlgebra/Solid/ComplexAdjunction.exactDerivedHomologyIso`
- Dependency: [D5/S3/HomologicalAlgebra/Solid/Definitions](Definitions.md)
