# Copied-Record Measurement Marginals

## Abstract

A copied address record makes the traced system marginal off-diagonal-free.

Library-search note: local mathlib and D5 searches for partial trace, environment marginal, unread state, pinching, Lueders, and projective measurement found no theorem identifying this concrete copied-record marginal with an unread measurement map. The proofs reuse the EnvironmentRecords definitions and finite-sum lemmas from mathlib.

Interface deviation: Conditioning is absent from this worktree's origin/dev base. This module does not duplicate IsRecordMeasurement or unreadState; it states the concrete address-block sum directly. The generic controlled-record trace identity is owned by EnvironmentRecords. Once Conditioning lands, a downstream bridge may identify the block sum with its canonical unread state.

Unresolved: a multiple-environment statement requires a joint state over all copy factors, a subsystem partial trace, and an explicit erasure operation. Those generic quantum constructions are deferred to an environment-infrastructure round rather than postulated in this Observer module.

**Theorem 1.1 (Copied-record marginal is the address-block sum).**

$$\forall \rho,\ \operatorname{tr}_{E}(J_{copy}(\rho))=\sum_{a\in\operatorname{Fin}(2)}P_{a} \rho P_{a}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasurementMarginal.copied_record_partial_trace_eq_address_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The copiedAddressRecord is the delta record that writes system address i into the matching environment address. Its Gram overlaps are one on equal addresses and zero otherwise. The retained system marginal is therefore the sum of P_a rho P_a over the two address projectors. The formula is stated directly so Conditioning remains the sole owner of the unread-state definition.

**Theorem 1.2 (One copied address record has zero off-diagonal marginal).**

$$\forall \rho,i,j,\ i\neq j \Rightarrow (\operatorname{tr}_{E}J_{copy}(\rho))_{ij}=0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasurementMarginal.copied_record_partial_trace_offDiagonal_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem starts with the explicit controlledRecordJointState for the delta record and applies traceEnvironment. The derived address-block identity leaves only diagonal system entries, so every entry with i distinct from j is zero.

## References

- Truth anchor: `D5/S3/Observer/MeasurementMarginal.copied_record_partial_trace_eq_address_blocks`
- Truth anchor: `D5/S3/Observer/MeasurementMarginal.copied_record_partial_trace_offDiagonal_eq_zero`
- Dependency: [D5/S3/Quantum/EnvironmentRecords](../Quantum/EnvironmentRecords.md)
