# Signed Integer Occupations

## Abstract

Signed integer-frequency occupations with occurrence parity and an absolute product majorant.

**Theorem 1.1 (Square-root norm majorant).**

Lean statement: `D5/S3/Combinatorics/Partitions/AnalyticIntegerOccupation.sqrt_norm_majorant`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/AnalyticIntegerOccupation.sqrt_norm_majorant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite colour type and complex q with norm q < 1, the norm of the signed integer occupation monomial is bounded by the square root norm raised to the public odd occupation energy. The proof uses occurrence parity for the sign and oddEnergy_le_twice_integerEnergy for the exponent comparison.

**Theorem 1.2 (Absolute occupation summability).**

Lean statement: `D5/S3/Combinatorics/Partitions/AnalyticIntegerOccupation.summable_norm_signed_integer_occupations`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/AnalyticIntegerOccupation.summable_norm_signed_integer_occupations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The square-root majorant and the public odd occupation summability theorem give absolute summability, including q = 0 and the empty colour type.

**Theorem 1.3 (Signed integer occupation product).**

Lean statement: `D5/S3/Combinatorics/Partitions/AnalyticIntegerOccupation.hasProd_signed_integer_occupations`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/AnalyticIntegerOccupation.hasProd_signed_integer_occupations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public occupation HasProd theorem is applied to z(i,k) = -q^(k+1). The product retains complex phases and occurrence parity; no energy-parity replacement is made.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/AnalyticIntegerOccupation.hasProd_signed_integer_occupations`
- Truth anchor: `D5/S3/Combinatorics/Partitions/AnalyticIntegerOccupation.sqrt_norm_majorant`
- Truth anchor: `D5/S3/Combinatorics/Partitions/AnalyticIntegerOccupation.summable_norm_signed_integer_occupations`
- Dependency: [D5/S3/Combinatorics/Partitions/AnalyticOddOccupation](AnalyticOddOccupation.md)
