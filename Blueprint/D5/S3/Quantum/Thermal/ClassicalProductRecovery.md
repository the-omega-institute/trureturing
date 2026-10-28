# ClassicalProductRecovery

## Abstract

Explicit ClassicalProductRecovery constructions. The linked declarations do not certify unproved analytic or quantum extensions.

**Theorem 1.1 (product recovery chain).**

Lean statement: `D5/S3/Quantum/Thermal/ClassicalProductRecovery.product_recovery_chain`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/ClassicalProductRecovery.product_recovery_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applies the pinned Mathlib measure-level KL chain rule to a constant hidden thermal kernel. Infinite values are retained rather than silently mapped to a finite divergence.

**Theorem 1.2 (recovery terms finite).**

Lean statement: `D5/S3/Quantum/Thermal/ClassicalProductRecovery.recovery_terms_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/ClassicalProductRecovery.recovery_terms_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proves finiteness of both summands from finite total KL before any real-valued subtraction is performed.

**Theorem 1.3 (recovery defect real).**

Lean statement: `D5/S3/Quantum/Thermal/ClassicalProductRecovery.recovery_defect_real`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/ClassicalProductRecovery.recovery_defect_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Converts the ENNReal chain identity to a real deficit only after proving both summands finite.

**Theorem 1.4 (thermalLift minimizes).**

Lean statement: `D5/S3/Quantum/Thermal/ClassicalProductRecovery.thermalLift_minimizes`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/ClassicalProductRecovery.thermalLift_minimizes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constructed product lift attains the marginal KL and no Markov-disintegrated joint law with that marginal has smaller KL.

**Theorem 1.5 (thermalLift unique minimum).**

Lean statement: `D5/S3/Quantum/Thermal/ClassicalProductRecovery.thermalLift_unique_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/ClassicalProductRecovery.thermalLift_unique_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cancels only a finite marginal KL. Equality of objective values forces equality of the actual joint measures, using the genuine converse Gibbs inequality.

**Theorem 1.6 (predictive defect invariant).**

Lean statement: `D5/S3/Quantum/Thermal/ClassicalProductRecovery.predictive_defect_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/ClassicalProductRecovery.predictive_defect_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An actual commuting observation/evolution square, with preserved reference measures, preserves both full and observed KL. It does not construct the Hamiltonian flow or a Gaussian disintegration.

## References

- Truth anchor: `D5/S3/Quantum/Thermal/ClassicalProductRecovery.predictive_defect_invariant`
- Truth anchor: `D5/S3/Quantum/Thermal/ClassicalProductRecovery.product_recovery_chain`
- Truth anchor: `D5/S3/Quantum/Thermal/ClassicalProductRecovery.recovery_defect_real`
- Truth anchor: `D5/S3/Quantum/Thermal/ClassicalProductRecovery.recovery_terms_finite`
- Truth anchor: `D5/S3/Quantum/Thermal/ClassicalProductRecovery.thermalLift_minimizes`
- Truth anchor: `D5/S3/Quantum/Thermal/ClassicalProductRecovery.thermalLift_unique_minimum`
