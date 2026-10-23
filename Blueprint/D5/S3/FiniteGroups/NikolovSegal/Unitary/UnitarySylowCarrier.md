# Unitary Sylow Carrier

## Abstract

Actual unitary sylow carrier supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.

**Definition 1.1 (specialUnitary).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowCarrier.specialUnitary`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowCarrier.specialUnitary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal determinant-one anti-diagonal unitary group: fixed points of the accepted field/inverse-transpose Steinberg automorphism on actual SL.

**Definition 1.2 (positiveU).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowCarrier.positiveU`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowCarrier.positiveU` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exactly the literal positive unitriangular matrices in actual SU.

**Theorem 1.3 (unitriangular iff depth).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowCarrier.unitriangular_iff_depth`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowCarrier.unitriangular_iff_depth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The parameterized unitriangular iff depth statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown.

**Theorem 1.4 (mem positiveU iff).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowCarrier.mem_positiveU_iff`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowCarrier.mem_positiveU_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The parameterized mem positiveU iff statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown.

**Theorem 1.5 (positiveU isPGroup).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowCarrier.positiveU_isPGroup`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowCarrier.positiveU_isPGroup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

P-group recognition reuses the accepted actual SLn theorem by injection.

The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowCarrier.mem_positiveU_iff`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowCarrier.positiveU`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowCarrier.positiveU_isPGroup`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowCarrier.specialUnitary`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowCarrier.unitriangular_iff_depth`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer](../TypeA/RootGeometry/PartIISLnUnipotentNormalizer.md)
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow](../TypeA/RootGeometry/PartIISLnUnipotentSylow.md)
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryTorusSupply](PartIIUnitaryTorusSupply.md)
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoGeometry](UnitaryRankTwoGeometry.md)
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryTraceRoot](UnitaryTraceRoot.md)
