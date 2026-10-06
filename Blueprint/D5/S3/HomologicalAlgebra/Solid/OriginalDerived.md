# Original Derived

## Abstract

Copyright (c) 2026. Released under the Apache 2.0 license. Exact original derived-constructor declarations of LeanEval `derived_solidification_free_CW_homology`, using the genuine unbounded D(Solid) realization and accepted exact Kan proof. No derived-existence, resolution, full-faithfulness or adjunction hypothesis is introduced. The original ordinary declarations are imported unchanged from CWSolid.Early. Challenge attribution: dagurtomas/LeanCondensed at 339ecc99fdc4bdb68ef248c16da0148dce61a639 (Apache-2.0).

Derived solidification is constructed on arbitrary unbounded cochain complexes. The literal derived inclusion has a left adjoint, whose ordinary-unit-induced comparison satisfies the total-left-derived and right-Kan-extension universal properties for all quasi-isomorphisms. The realization uses a projective generator, augmented resolutions and both unbounded truncation telescopes.

**Definition 1.1 (derived Solidification).**

Lean statement: `D5/S3/HomologicalAlgebra/Solid/OriginalDerived.derivedSolidification`

*Formalization.* `D5/S3/HomologicalAlgebra/Solid/OriginalDerived.derivedSolidification` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

**Hole 4.** The derived solidification functor.

**Definition 1.2 (derived Solidification Counit).**

Lean statement: `D5/S3/HomologicalAlgebra/Solid/OriginalDerived.derivedSolidificationCounit`

*Formalization.* `D5/S3/HomologicalAlgebra/Solid/OriginalDerived.derivedSolidificationCounit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

**Hole 5.** The comparison map from derived solidification to degreewise solidification.

**Theorem 1.3 (derived Solidification is Left Derived Functor).**

Lean statement: `D5/S3/HomologicalAlgebra/Solid/OriginalDerived.derivedSolidification_isLeftDerivedFunctor`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/Solid/OriginalDerived.derivedSolidification_isLeftDerivedFunctor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

**Hole 6.** Derived solidification, together with the comparison map of the previous hole, is the total left derived functor of degreewise solidification followed by localization.

**Definition 1.4 (derived Solidification Adjunction).**

Lean statement: `D5/S3/HomologicalAlgebra/Solid/OriginalDerived.derivedSolidificationAdjunction`

*Formalization.* `D5/S3/HomologicalAlgebra/Solid/OriginalDerived.derivedSolidificationAdjunction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

**Hole 7.** The derived solidification adjunction: derived solidification is left adjoint to the derived inclusion.

**Theorem 1.5 (solidification has Left Derived Functor).**

Lean statement: `D5/S3/HomologicalAlgebra/Solid/OriginalDerived.solidification_hasLeftDerivedFunctor`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/Solid/OriginalDerived.solidification_hasLeftDerivedFunctor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual existence for all quasi-isomorphisms of arbitrary unbounded complexes.

**Theorem 1.6 (derived Solidification is Right Kan Extension).**

Lean statement: `D5/S3/HomologicalAlgebra/Solid/OriginalDerived.derivedSolidification_isRightKanExtension`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/Solid/OriginalDerived.derivedSolidification_isRightKanExtension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original counit has the literal right-Kan-extension universal property.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/Solid/OriginalDerived.derivedSolidification`
- Truth anchor: `D5/S3/HomologicalAlgebra/Solid/OriginalDerived.derivedSolidificationAdjunction`
- Truth anchor: `D5/S3/HomologicalAlgebra/Solid/OriginalDerived.derivedSolidificationCounit`
- Truth anchor: `D5/S3/HomologicalAlgebra/Solid/OriginalDerived.derivedSolidification_isLeftDerivedFunctor`
- Truth anchor: `D5/S3/HomologicalAlgebra/Solid/OriginalDerived.derivedSolidification_isRightKanExtension`
- Truth anchor: `D5/S3/HomologicalAlgebra/Solid/OriginalDerived.solidification_hasLeftDerivedFunctor`
- Dependency: [D5/S3/HomologicalAlgebra/Solid/AdjunctionKanExtension](AdjunctionKanExtension.md)
- Dependency: [D5/S3/HomologicalAlgebra/Solid/RealizedAdjunction](RealizedAdjunction.md)
