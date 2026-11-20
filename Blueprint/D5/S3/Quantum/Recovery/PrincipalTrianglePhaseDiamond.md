# Native stabilized channel witness for the principal phase bound

## Abstract

A tagged pure input realizes a lossless matrix-unit test for the unhalved native diamond distance.

**Theorem 1.1 (Lossless matrix-unit test).**

Lean statement: `D5/S3/Quantum/Recovery/PrincipalTrianglePhaseDiamond.matrixUnit_le_diamondDistance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PrincipalTrianglePhaseDiamond.matrixUnit_le_diamondDistance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two reference tags yield half of the tested matrix-unit coefficient in the output cross block. The pair of phase-swap unitaries recovers its doubled modulus in the Hermitian output difference, so the two scales cancel exactly. This proof uses the native density-state supremum, without a non-Hermitian input convention.

**Theorem 1.2 (Native diamond-distance phase lower bound).**

Lean statement: `D5/S3/Quantum/Recovery/PrincipalTrianglePhaseDiamond.near_real_diamond_lower_of_dominance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PrincipalTrianglePhaseDiamond.near_real_diamond_lower_of_dominance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified channel coefficient correspondence and cross-entry dominance of the records, the native unhalved diamond distance obeys the quadratic near-real bound. The coefficient correspondence and the dominance are hypotheses: no arbitrary-channel reduction or unrestricted recovery obstruction is claimed.

**Theorem 1.3 (Paired-dilation application).**

Lean statement: `D5/S3/Quantum/Recovery/PrincipalTrianglePhaseDiamond.paired_near_real_diamond_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PrincipalTrianglePhaseDiamond.paired_near_real_diamond_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Gram of the actual correct-output dilation coordinates is positive. For an isometric dilation, the Gram of the omitted coordinates gives its within-fibre defect, without a no-leakage assumption. The two forward records produce the tested paired coefficient with the displayed conjugation, while channel and target identification remain hypotheses.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/PrincipalTrianglePhaseDiamond.matrixUnit_le_diamondDistance`
- Truth anchor: `D5/S3/Quantum/Recovery/PrincipalTrianglePhaseDiamond.near_real_diamond_lower_of_dominance`
- Truth anchor: `D5/S3/Quantum/Recovery/PrincipalTrianglePhaseDiamond.paired_near_real_diamond_lower`
- Dependency: [D5/S3/Quantum/Foundation/FiniteDiamondDistance](../Foundation/FiniteDiamondDistance.md)
- Dependency: [D5/S3/Quantum/Recovery/PrincipalTrianglePhaseBound](PrincipalTrianglePhaseBound.md)
