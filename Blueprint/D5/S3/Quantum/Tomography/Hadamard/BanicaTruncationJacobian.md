# Fourier phase Jacobian

## Abstract

Analytic Fourier phase equations, their real derivative, and the dimension of its kernel.

**Definition 1.1 (Ordered row pairs).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.RowPairs`

*Formalization.* `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.RowPairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each pair of distinct rows is represented once by placing the lesser row first.

**Definition 1.2 (Real phase coordinates).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.phaseMatrix`

*Formalization.* `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.phaseMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each matrix entry is multiplied by exp(i theta). The phase parameters are real.

**Definition 1.3 (Orthogonality residual).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.phaseResidual`

*Formalization.* `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.phaseResidual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The upper triangular row inner products are expressed as finite sums of weighted exponential phase differences.

**Definition 1.4 (Real phase Jacobian).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.phaseJacobian`

*Formalization.* `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.phaseJacobian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The continuous real linear map sums the weighted infinitesimal phase differences for every independent row pair.

**Theorem 1.5 (Analytic phase equations).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.phase_residual_contDiff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.phase_residual_contDiff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual exponential residual is real analytic on the entire real phase space.

**Theorem 1.6 (Derivative of the residual).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.phase_residual_hasFDerivAt_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.phase_residual_hasFDerivAt_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At zero phase the Frechet derivative of the actual residual is the displayed phase Jacobian.

**Theorem 1.7 (Jacobian coordinate formula).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.phase_jacobian_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.phase_jacobian_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each Jacobian coordinate is i times the sum of the original row product weighted by the difference of the two row velocities.

**Definition 1.8 (Row and column phases).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.rowColumnMap`

*Formalization.* `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.rowColumnMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The linear map sends a pair of real row and column parameter functions to their sum at each matrix entry.

**Theorem 1.9 (Row and column dimension bound).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.row_column_finrank_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.row_column_finrank_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real dimension of the row and column phase space is at most the sum of the numbers of rows and columns.

**Definition 1.10 (Fourier characters).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.fourierMatrix`

*Formalization.* `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.fourierMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Fourier row indexed by s has jth entry given by the standard additive character at s j.

**Theorem 1.11 (Surjectivity after row deletion).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.fourier_jacobian_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.fourier_jacobian_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For prime modulus and a proper row subset, every independent complex orthogonality velocity is attained by a real phase velocity. A missing vertex cuts each nonzero frequency circle into paths. Integrating the prescribed edge data and applying inverse discrete Fourier transform produces a complex solution. Taking its real part after conjugate symmetrization preserves the requested velocities.

**Theorem 1.12 (Number of orthogonality equations).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.row_pairs_card_twice`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.row_pairs_card_twice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Twice the number of ordered independent row pairs is the product of the row count and one less than the row count.

**Theorem 1.13 (Exact kernel dimension).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.phase_jacobian_rank_nullity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.phase_jacobian_rank_nullity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a surjective phase Jacobian, the real dimension of its kernel plus m(m-1) equals m n. The independent complex equations contribute two real coordinates each.

**Theorem 1.14 (A direction beyond row and column phases).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.phase_jacobian_kernel_nontrivial`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.phase_jacobian_kernel_nontrivial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the number of phase variables exceeds the real equation count plus the row and column parameter count, rank-nullity supplies a Jacobian kernel vector outside the row and column phase space.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.RowPairs`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.fourierMatrix`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.fourier_jacobian_surjective`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.phaseJacobian`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.phaseMatrix`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.phaseResidual`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.phase_jacobian_apply`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.phase_jacobian_kernel_nontrivial`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.phase_jacobian_rank_nullity`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.phase_residual_contDiff`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.phase_residual_hasFDerivAt_zero`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.rowColumnMap`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.row_column_finrank_le`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian.row_pairs_card_twice`
- Dependency: [D5/S3/Quantum/Tomography/Hadamard/BanicaCycleForestIncidence](BanicaCycleForestIncidence.md)
