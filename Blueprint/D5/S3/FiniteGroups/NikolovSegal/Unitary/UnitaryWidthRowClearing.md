# Unitary Width Row Clearing

## Abstract

Actual unitary width row clearing supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.

**Definition 1.1 (middle).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRowClearing.middle`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRowClearing.middle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The parameterized middle statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown.

**Theorem 1.2 (clear last row).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRowClearing.clear_last_row`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRowClearing.clear_last_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A unit last pivot permits one genuine lower-SU operation to clear the entire last row. The central quadratic corner is retained in every characteristic.

**Theorem 1.3 (last row reduction).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRowClearing.last_row_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRowClearing.last_row_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Four alternating actual SU operations put any target into the genuine last-row stabilizer, uniformly in rank and field.

The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRowClearing.clear_last_row`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRowClearing.last_row_reduction`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRowClearing.middle`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalTraceCoordinates](PartIIUnitaryRadicalTraceCoordinates.md)
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthPivot](UnitaryWidthPivot.md)
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthTranspose](UnitaryWidthTranspose.md)
