# Failure probabilities from finite nets

## Abstract

Finite net bounds for Schmidt and operator tails of Hermitian sign matrices.

**Theorem 1.1 (Schmidt bound tail).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixNetBounds.signCubeSample_schmidt_failure_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixNetBounds.signCubeSample_schmidt_failure_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sum the fixed-pair bilinear tail bounds over the Cartesian square of the Schmidt net.

**Theorem 1.2 (Operator norm tail from quadratic tails).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixNetBounds.operator_tail_of_quadratic_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixNetBounds.operator_tail_of_quadratic_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Bound the probability of a norm threshold by the union of fixed-vector quadratic events on a net of the full sphere.

**Theorem 1.3 (Sign cube sample operator tail).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixNetBounds.signCubeSample_operator_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixNetBounds.signCubeSample_operator_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonnegative threshold, the ordinary sign matrix operator tail follows from the finite full-sphere net and the fixed-vector quadratic tail.

**Theorem 1.4 (Sign cube sample partial transpose operator tail of quadratic).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixNetBounds.signCubeSample_partialTranspose_operator_tail_of_quadratic`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixNetBounds.signCubeSample_partialTranspose_operator_tail_of_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same finite net converts a uniform fixed-vector quadratic tail for the partial transpose into an operator tail for the partial transpose.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixNetBounds.operator_tail_of_quadratic_tail`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixNetBounds.signCubeSample_operator_tail`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixNetBounds.signCubeSample_partialTranspose_operator_tail_of_quadratic`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixNetBounds.signCubeSample_schmidt_failure_le`
- Dependency: [D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails](FiniteSignTails.md)
- Dependency: [D5/S3/Quantum/Entanglement/EntanglementBreaking/NetInterpolation](NetInterpolation.md)
