# Phase normalization

## Abstract

Unit complex phases normalize the off-diagonal trace without changing the spectral problem.

**Theorem 1.1 (Block positivity under a unit phase).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/PhaseRotation.block_posSemidef_phase`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/PhaseRotation.block_posSemidef_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For every dimension and positive semidefinite block matrix with diagonal blocks A,B and off-diagonal blocks X,X adjoint, every complex z of modulus one gives another positive semidefinite block matrix with off-diagonal blocks zX and its adjoint. Conjugation by the block diagonal matrix diag(zI,I) gives this matrix exactly and leaves both diagonal blocks fixed.

**Theorem 1.2 (Unit phases preserve singular values).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/PhaseRotation.singularValuesSorted_phase`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/PhaseRotation.singularValuesSorted_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For every finite complex square matrix X, every complex z of modulus one and every decreasing singular-value index j, the j-th singular values of zX and X coincide. This is the existing unitary invariance theorem applied to zI.

**Theorem 1.3 (Real nonnegative trace normalization).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/PhaseRotation.exists_trace_phase`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/PhaseRotation.exists_trace_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For every finite complex square matrix X there is a complex z of modulus one such that tr(zX)=|tr(X)|. The scalar polar-phase existence theorem includes zero trace. Trace linearity gives the matrix statement. Together the three statements let the arithmetic singular-value argument use a real nonnegative trace without changing positivity or singular values.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/PhaseRotation.block_posSemidef_phase`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/PhaseRotation.exists_trace_phase`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/PhaseRotation.singularValuesSorted_phase`
- Dependency: [D5/S3/Quantum/Schatten/SingularValueOrder](../../Schatten/SingularValueOrder.md)
