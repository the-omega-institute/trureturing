# Unitary Width Endpoint Stabilizer

## Abstract

Actual unitary width endpoint stabilizer supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.

**Theorem 1.1 (inverse coordinate row).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthEndpointStabilizer.inverse_coordinate_row`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthEndpointStabilizer.inverse_coordinate_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fixing a literal coordinate row also fixes that row in the actual inverse.

**Theorem 1.2 (reflected coordinate column).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthEndpointStabilizer.reflected_coordinate_column`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthEndpointStabilizer.reflected_coordinate_column` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The other endpoint is forced by actual SU fixedness, not a flag premise.

**Theorem 1.3 (four operations endpoint stabilizer).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthEndpointStabilizer.four_operations_endpoint_stabilizer`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthEndpointStabilizer.four_operations_endpoint_stabilizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One absolute four-operation Hermitian elimination puts every actual SU matrix of dimension≥4 in the two-endpoint stabilizer. Both endpoint equalities are derived. This is a rank-reduction bridge, not a full width theorem.

The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthEndpointStabilizer.four_operations_endpoint_stabilizer`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthEndpointStabilizer.inverse_coordinate_row`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthEndpointStabilizer.reflected_coordinate_column`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRowClearing](UnitaryWidthRowClearing.md)
