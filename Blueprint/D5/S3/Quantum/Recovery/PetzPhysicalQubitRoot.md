# Normalized square root of a physical flag

## Abstract

Normalized square root of a physical flag.

**Theorem 1.1 (Faithful flag block).**

Lean statement: `D5/S3/Quantum/Recovery/PetzPhysicalQubitRoot.unscaledBlock_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzPhysicalQubitRoot.unscaledBlock_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive determinant and positive first diagonal entry give a triangular factorization of the unscaled flag block.

**Theorem 1.2 (Exact normalized square root).**

Lean statement: `D5/S3/Quantum/Recovery/PetzPhysicalQubitRoot.normalizedRoot_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzPhysicalQubitRoot.normalizedRoot_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace and determinant identities for the positive qubit square root determine its scalar denominator and all four entries after the marginal normalization.

**Theorem 1.3 (Derivative at the diagonal flag).**

Lean statement: `D5/S3/Quantum/Recovery/PetzPhysicalQubitRoot.normalizedRoot_firstVariation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzPhysicalQubitRoot.normalizedRoot_firstVariation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant and denominator have zero derivative at the base. The upper and lower off-diagonal entries have different slopes because the inverse half-power acts on the right.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/PetzPhysicalQubitRoot.normalizedRoot_firstVariation`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzPhysicalQubitRoot.normalizedRoot_formula`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzPhysicalQubitRoot.unscaledBlock_posDef`
- Dependency: [D5/S3/Quantum/CommutingMidpoint/Fidelity](../CommutingMidpoint/Fidelity.md)
- Dependency: [D5/S3/Quantum/Matrix/SpectralPower](../Matrix/SpectralPower.md)
