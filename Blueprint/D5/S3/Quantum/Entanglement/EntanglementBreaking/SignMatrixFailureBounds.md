# Dimension thresholds for the three bad events

## Abstract

The three finite sign failure bounds at the admissible dimensions.

**Theorem 1.1 (Schmidt failure bound below one quarter).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixFailureBounds.schmidt_failure_bound_lt_quarter`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixFailureBounds.schmidt_failure_bound_lt_quarter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k at least two and d at least 524288 times k cubed, the quadratic tail exponent dominates the logarithmic net-size contribution with strict margin.

**Theorem 1.2 (Operator failure bound below one quarter).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixFailureBounds.operator_failure_bound_lt_quarter`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixFailureBounds.operator_failure_bound_lt_quarter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For d at least four, the exponent for threshold 3d dominates the logarithmic sphere-net contribution. This numerical bound is used for both operator events.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixFailureBounds.operator_failure_bound_lt_quarter`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixFailureBounds.schmidt_failure_bound_lt_quarter`
- Dependency: [D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixNetBounds](SignMatrixNetBounds.md)
