# Stability of diagonal BKM recovery

## Abstract

Trace preservation, positivity and log-conditioned trace-norm stability for diagonal BKM recovery.

**Definition 1.1 (Actual BKM recovery on the diagonal algebra).**

Lean statement: `D5/S3/Quantum/Recovery/BKMDiagonalStability.diagonalRecovery`

*Formalization.* `D5/S3/Quantum/Recovery/BKMDiagonalStability.diagonalRecovery` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fix the coordinate diagonal of a finite complex matrix algebra. For a positive definite reference a and diagonal B, divide each B_ii by a_ii and apply the BKM power integral Omega_a to the resulting diagonal matrix.

**Theorem 1.2 (Two-sided inverse on the diagonal algebra).**

Lean statement: `D5/S3/Quantum/Recovery/BKMDiagonalStability.diagonalOmegaInverse_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMDiagonalStability.diagonalOmegaInverse_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive definite a, Omega_diag(a) multiplies the i-th diagonal entry by a_ii. Coordinate division gives both inverse identities on every complex diagonal B.

**Theorem 1.3 (Complex trace preservation).**

Lean statement: `D5/S3/Quantum/Recovery/BKMDiagonalStability.diagonalRecovery_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMDiagonalStability.diagonalRecovery_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive definite reference a and any complex diagonal input B, the trace of recovery equals the trace of B. The trace of Omega_a(C) equals the trace of aC, and multiplication by a cancels the diagonal division inside the trace.

**Definition 1.4 (Diagonal density matrices).**

Lean statement: `D5/S3/Quantum/Recovery/BKMDiagonalStability.DiagonalTest`

*Formalization.* `D5/S3/Quantum/Recovery/BKMDiagonalStability.DiagonalTest` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The tests are all diagonal positive semidefinite matrices of ordinary trace one, including singular matrices.

**Theorem 1.5 (Negative spectral mass).**

Lean statement: `D5/S3/Quantum/Recovery/BKMDiagonalStability.diagonalRecovery_negativeTrace_eq_spectral`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMDiagonalStability.diagonalRecovery_negativeTrace_eq_spectral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive definite reference and any diagonal test, recovery produces a Hermitian matrix. Half the difference between its trace norm and real trace equals the sum of the magnitudes of its negative eigenvalues.

**Definition 1.6 (Defect over diagonal tests).**

Lean statement: `D5/S3/Quantum/Recovery/BKMDiagonalStability.diagonalRecoveryDefect`

*Formalization.* `D5/S3/Quantum/Recovery/BKMDiagonalStability.diagonalRecoveryDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The recovery defect is the supremum of the negative spectral mass over the diagonal density matrices.

**Theorem 1.7 (Rank-one attainment).**

Lean statement: `D5/S3/Quantum/Recovery/BKMDiagonalStability.diagonalRecoveryDefect_isGreatest`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMDiagonalStability.diagonalRecoveryDefect_isGreatest` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In nonzero finite dimension, for every positive definite a, one coordinate projector of rank one attains the greatest negative spectral mass. Each diagonal test is a convex combination of these projectors. Linearity of recovery and convexity of the negative trace formula bound its defect by the largest coordinate value.

**Theorem 1.8 (Capped log-conditioned estimate).**

Lean statement: `D5/S3/Quantum/Recovery/BKMDiagonalStability.actual_maximal_abelian_bkm_stability`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMDiagonalStability.actual_maximal_abelian_bkm_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a be a positive definite trace-one matrix on any nonempty finite index type. Write d for its dimension, X for d times a, and T for the logarithm of the ratio of the largest to the smallest eigenvalue of X. With epsilon the recovery defect of a, the unhalved trace norm of a minus diag(X)/d is at most the minimum of 2 and sqrt((12 + T^2) epsilon (1 + epsilon)). Dimension one and repeated eigenvalues are included. The logarithmic mean estimate controls spectral variance through each coordinate output's negative trace, and weighted column bounds give the trace norm. The cap follows from the unit traces of a and its diagonal.

**Theorem 1.9 (Positivity characterizes diagonal references).**

Lean statement: `D5/S3/Quantum/Recovery/BKMDiagonalStability.diagonalRecovery_positive_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMDiagonalStability.diagonalRecovery_positive_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive definite trace-one reference on a nonempty finite index type, all diagonal density matrices have positive semidefinite recovered outputs exactly when a is diagonal. Positivity forces zero defect, and stability and trace-norm faithfulness force a to equal its diagonal. For a diagonal reference the inverse identity fixes each diagonal input.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/BKMDiagonalStability.DiagonalTest`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMDiagonalStability.actual_maximal_abelian_bkm_stability`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMDiagonalStability.diagonalOmegaInverse_spec`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMDiagonalStability.diagonalRecovery`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMDiagonalStability.diagonalRecoveryDefect`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMDiagonalStability.diagonalRecoveryDefect_isGreatest`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMDiagonalStability.diagonalRecovery_negativeTrace_eq_spectral`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMDiagonalStability.diagonalRecovery_positive_iff`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMDiagonalStability.diagonalRecovery_trace`
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks](../Entanglement/PermutationCriteria/BellBlocks.md)
- Dependency: [D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM](../Entanglement/TavakoliMorelliIncompleteEAM.md)
- Dependency: [D5/S3/Quantum/Recovery/BKMRelativeDensity](BKMRelativeDensity.md)
- Dependency: [D5/S3/Quantum/Schatten/TraceNorm](../Schatten/TraceNorm.md)
