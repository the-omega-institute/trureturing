# Indecomposable maps from finite Hermitian signs

## Abstract

Simultaneous sign matrix bounds give indecomposable k-entanglement-breaking maps.

**Theorem 1.1 (Simultaneous bounds in the sign cube).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixConstruction.finiteSignSample_unconditional`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixConstruction.finiteSignSample_unconditional` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each of the three bad events has probability less than one quarter under the same uniform measure. One assignment lies outside their union. The norm bounds give positive semidefiniteness for both trace tests, and the Schmidt bound gives separability after local congruence.

**Theorem 1.2 (Indecomposable k-entanglement-breaking maps).**

$$\forall k \in \mathbb{N},\; \forall d \in \mathbb{N},\; \left(2 \le k \land 524288 \cdot k^{3} \le d\right) \Rightarrow \left(\exists f \in \operatorname{MatrixMap}\left(d, d\right),\; \operatorname{IsKEB}\left(k, f\right) \land \left(\neg \operatorname{IsDecomposable}\left(f\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixConstruction.exists_indecomposable_kEB` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each natural number k at least two and every natural number d at least 524288 times k cubed, there is a complex-linear k-entanglement-breaking map from the full d by d matrix algebra into itself that is indecomposable.

**Theorem 1.3 (Exists sign cube sample good).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixConstruction.exists_signCubeSample_good`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixConstruction.exists_signCubeSample_good` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k at least two and dimension at least 524288 times k cubed, a single assignment has the Schmidt-restricted quadratic bound and operator norms at most four times d for both the matrix and its output partial transpose.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixConstruction.exists_indecomposable_kEB`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixConstruction.exists_signCubeSample_good`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixConstruction.finiteSignSample_unconditional`
- Dependency: [D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixFailureBounds](SignMatrixFailureBounds.md)
- Dependency: [D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixPartialTranspose](SignMatrixPartialTranspose.md)
