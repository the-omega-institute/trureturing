# Exact Mates

## Abstract

Compatibility of an exact adjunction and its mates with the unbounded derived localization. New proofs, released under the Apache 2.0 license. The localization constructions used here are Mathlib's proved constructions.

**Theorem 1.1 (exact Adjunction Derived unit mate).**

Lean statement: `D5/S3/HomologicalAlgebra/Solid/ExactMates.exactAdjunctionDerived_unit_mate`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/Solid/ExactMates.exactAdjunctionDerived_unit_mate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A mate relation for an exact adjunction remains the same relation after unbounded derived localization. This is proved from the actual localized unit, rather than assumed as an additional adjunction compatibility.

**Theorem 1.2 (exact Adjunction Derived hom Equiv mate).**

Lean statement: `D5/S3/HomologicalAlgebra/Solid/ExactMates.exactAdjunctionDerived_homEquiv_mate`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/Solid/ExactMates.exactAdjunctionDerived_homEquiv_mate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the localized exact adjunction, precomposition by the left mate is postcomposition by the right mate. All derived objects are unbounded.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/Solid/ExactMates.exactAdjunctionDerived_homEquiv_mate`
- Truth anchor: `D5/S3/HomologicalAlgebra/Solid/ExactMates.exactAdjunctionDerived_unit_mate`
- Dependency: [D5/S3/HomologicalAlgebra/Solid/ExactFunctorNatTrans](ExactFunctorNatTrans.md)
