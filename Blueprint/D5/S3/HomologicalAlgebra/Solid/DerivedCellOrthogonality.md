# Derived Cell Orthogonality

## Abstract

The protected defining cells tested in the actual unbounded derived category. These proofs use only the exact tensor/internal-Hom adjunction for P, not a derived solidification adjunction. New proofs, Apache 2.0.

**Theorem 1.1 (solid Localization Cell derived Inclusion Hom zero).**

Lean statement: `D5/S3/HomologicalAlgebra/Solid/DerivedCellOrthogonality.solidLocalizationCell_derivedInclusionHom_zero`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/Solid/DerivedCellOrthogonality.solidLocalizationCell_derivedInclusionHom_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In particular, the actual defining cells have zero derived maps into the image of every unbounded solid complex.

**Theorem 1.2 (solid Cell Attachment derived Precomp bijective).**

Lean statement: `D5/S3/HomologicalAlgebra/Solid/DerivedCellOrthogonality.solidCellAttachment_derivedPrecomp_bijective`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/Solid/DerivedCellOrthogonality.solidCellAttachment_derivedPrecomp_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An actual attachment along one defining cell has a universal derived comparison against every derived-local target. This supplies both existence and uniqueness for derived maps (not only chain-map homotopies).

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/Solid/DerivedCellOrthogonality.solidCellAttachment_derivedPrecomp_bijective`
- Truth anchor: `D5/S3/HomologicalAlgebra/Solid/DerivedCellOrthogonality.solidLocalizationCell_derivedInclusionHom_zero`
- Dependency: [D5/S3/HomologicalAlgebra/Solid/CellLocality](CellLocality.md)
- Dependency: [D5/S3/HomologicalAlgebra/Solid/ExactMates](ExactMates.md)
- Dependency: [D5/S3/HomologicalAlgebra/Solid/FreeFlat](FreeFlat.md)
