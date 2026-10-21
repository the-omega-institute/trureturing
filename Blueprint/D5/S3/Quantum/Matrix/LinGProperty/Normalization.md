# Zero diagonal blocks

## Abstract

Zero diagonal blocks.

**Theorem 1.1 (Zero diagonal blocks).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/Normalization.offDiagonal_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/Normalization.offDiagonal_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

If a positive semidefinite matrix has blocks A, X, X-adjoint and B and either diagonal block vanishes, then X vanishes. Each cross entry has squared modulus bounded by the product of its two diagonal entries.

**Theorem 1.2 (Positive trace of a nonzero positive matrix).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/Normalization.positive_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/Normalization.positive_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

A nonzero positive semidefinite complex matrix has strictly positive real trace. Zero trace would force every eigenvalue, and hence the matrix, to vanish.

**Theorem 1.3 (Strict positivity after trace augmentation).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/Normalization.phi_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/Normalization.phi_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For c at least one, trace augmentation sends every nonzero positive semidefinite matrix to a positive definite matrix. Its scalar identity term has strictly positive coefficient.

**Theorem 1.4 (Homogeneity of trace augmentation).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/Normalization.phi_smul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/Normalization.phi_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

Real scaling commutes with the map T to T+c trace(T) I.

**Theorem 1.5 (Block congruence normalization).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/Normalization.block_scale_posSemidef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/Normalization.block_scale_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

Congruence by the block diagonal matrix with entries rI and sI preserves positivity and replaces A, X and B by r squared A, rs X and s squared B. Choosing inverse square roots of the diagonal traces normalizes both traces simultaneously.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/Normalization.block_scale_posSemidef`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/Normalization.offDiagonal_eq_zero`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/Normalization.phi_posDef`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/Normalization.phi_smul`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/Normalization.positive_trace`
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../CartesianVariance.md)
