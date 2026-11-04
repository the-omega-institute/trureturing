# Positive amplitude and exact functional calculus

## Abstract

The ordinary Petz factors of the six-dimensional reverse instance.

**Theorem 1.1 (A positive amplitude).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReversePetz.amplitude_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReversePetz.amplitude_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the binary-times-three-level coordinate order, Y is the positive diagonal (1,2,2,1,2,2) plus the four rank-one squares from e0+e3, e1-e4, e0+e2, and e3-e5. In particular Y is invertible.

**Theorem 1.2 (The output square root).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReversePetz.output_root`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReversePetz.output_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The physical channel output is Y squared divided by 62. Its positive square root is Y divided by sqrt(62), by uniqueness of the positive square root.

**Theorem 1.3 (Full output support).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReversePetz.output_support`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReversePetz.output_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The output is positive definite, so its functional-calculus support is the identity. The spectral inverse square root is sqrt(62) times the inverse of Y.

**Theorem 1.4 (The actual Petz operators).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReversePetz.petz_kraus_identification`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReversePetz.petz_kraus_identification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every one of the twelve environment labels, sqrt(rho) times the adjoint noise operator times the spectral inverse square root of the actual output equals the corresponding environment slice. Inactive labels give zero.

**Theorem 1.5 (The ordinary reference-completed Petz channel).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReversePetz.ordinary_petz_channel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReversePetz.ordinary_petz_channel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A channel supplied by the reference-completed Petz construction acts on every physical output matrix as the slice Kraus sum and recovers rho from the actual noise output. Full support makes the reference completion term zero on every input.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/BurriReversePetz.amplitude_positive`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReversePetz.ordinary_petz_channel`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReversePetz.output_root`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReversePetz.output_support`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReversePetz.petz_kraus_identification`
- Dependency: [D5/S3/Quantum/Recovery/BurriReverseOverlap](BurriReverseOverlap.md)
