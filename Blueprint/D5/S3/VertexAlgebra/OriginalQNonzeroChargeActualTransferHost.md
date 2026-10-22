# Nonzero-Charge Actual Original-Q Transfer

## Abstract

For every nonzero charge at critical rank 26, the actual original-Q fixed sector has a derived finite quartet transfer and true quotient equivalence.

**Theorem 1.1 (Actual nonzero-charge transfer with derived frame and mass-shell differential).**

Lean statement: `D5/S3/VertexAlgebra/OriginalQNonzeroChargeActualTransferHost.actual_nonzero_charge_original_q_transfer`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalQNonzeroChargeActualTransferHost.actual_nonzero_charge_original_q_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem assumes critical rank 26, both left and right Gram inverse equations, a nonzero integral charge, and an arbitrary integer level. The private host detects a null direction on which the charge is nonzero, derives its adapted partner, and assembles an invertible literal-dual frame with both inverse equations and both dual-row identities. No fixed null direction or frame-existence hypothesis is supplied.

The constructed frame is consumed by the actual fixed-charge fixed-energy original-Q sector, finite inverse, transfer inclusion, projection, homotopy, and transferred differential. The returned true cohomology equivalence is for the actual kernel modulo the actual range, with the exact finite cutoff 2 * level.toNat + 2 for every integer level.

For every actual state satisfying the charge-sector and exact energy equations, the returned differential is (chosenH D beta + (level : Complex) - 1) smul C D 0 applied to the projected state. The statement preserves the distinction between C D 0 killing projected Q and C D 0 killing the whole projected range.

The private frame assembly consumes isotropic separation and the literal-dual basis construction inside this substantive actual-Q consumer. Ambient/global and zero-charge branches remain separate obligations; no full-string, anomaly, fusion, or AdS/CFT completion is asserted.

## References

- Truth anchor: `D5/S3/VertexAlgebra/OriginalQNonzeroChargeActualTransferHost.actual_nonzero_charge_original_q_transfer`
