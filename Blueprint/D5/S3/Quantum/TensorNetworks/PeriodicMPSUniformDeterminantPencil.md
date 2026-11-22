# The contracted flattening and the witness pencil

## Abstract

A determinant pencil from the full periodic trace tensor

**Theorem 1.1 (The determinant of the contracted flattening).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformDeterminantPencil.det_observedFlattening_traceWord`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformDeterminantPencil.det_observedFlattening_traceWord` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose four prefix words and four suffix words around a single physical slot. Contract that slot against a two-vector z. For a periodic binary bond-two trace tensor the resulting determinant is the product of the two guard-coordinate determinants and the square of the determinant of z₀A₀ + z₁A₁. The trace pairing factors the flattening through right multiplication by the pencil, which acts as the pencil on one of the two bond indices.

**Definition 1.2 (The two witness cores).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformDeterminantPencil.witnessCore`

*Formalization.* `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformDeterminantPencil.witnessCore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The zero core has first row (1, 0) and vanishing second row. The one core has rows (1, 1) and (−1, −1). Both are rank one. The zero core is idempotent, so padding a guard with further zeros leaves its product unchanged.

**Theorem 1.3 (The witness quartic at every length).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformDeterminantPencil.det_guardedFlattening_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformDeterminantPencil.det_guardedFlattening_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n ≥ 7, the prescribed guards are indexed by their endpoint bits, with one interior zero on the left and n − 6 on the right. The witness pencil has determinant −z₀z₁. Idempotence reduces the guards to the same four-by-four calculation at every length. Evaluation at z = (1, 1) gives determinant −1 and fixes the full-tensor flattening determinant to −(z₀z₁)².

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformDeterminantPencil.det_guardedFlattening_witness`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformDeterminantPencil.det_observedFlattening_traceWord`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformDeterminantPencil.witnessCore`
