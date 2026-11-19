# Coherent block budget for the one-party plaquette obstruction

## Abstract

Coherent rows strengthen the one-party plaquette obstruction for native paired channels.

**Theorem 1.1 (One squared diamond budget per coefficient row).**

Lean statement: `D5/S3/Quantum/Recovery/PrincipalPlaquetteBlockBudget.matrixUnit_row_square_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PrincipalPlaquetteBlockBudget.matrixUnit_row_square_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A tagged rank-one test chooses the column amplitude vector proportional to all the errors in the row. It bounds their squared norm sum by the square of the native unhalved diamond distance.

**Theorem 1.2 (Improved one-party phase bound from coherent rows).**

Lean statement: `D5/S3/Quantum/Recovery/PrincipalPlaquetteBlockBudget.paired_improved_one_party_native_diamond`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PrincipalPlaquetteBlockBudget.paired_improved_one_party_native_diamond` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For one selected pair of fibres the two row tests give a Frobenius budget. The opposite gauge converts entry errors into signed real budget deficits; a reciprocal-weight Cauchy bound then strengthens the cosine obstruction by a factor of twelve elevenths.

Only the first party's phase is used. The native paired-channel identity, labelled fibres and original target coefficients remain hypotheses. No assumption on leakage, common quotient or cross-entry dominance is added.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/PrincipalPlaquetteBlockBudget.matrixUnit_row_square_le`
- Truth anchor: `D5/S3/Quantum/Recovery/PrincipalPlaquetteBlockBudget.paired_improved_one_party_native_diamond`
- Dependency: [D5/S3/Quantum/Recovery/PrincipalPlaquettePhaseDiamond](PrincipalPlaquettePhaseDiamond.md)
- Dependency: [D5/S3/Quantum/Recovery/PrincipalTrianglePhaseDiamond](PrincipalTrianglePhaseDiamond.md)
