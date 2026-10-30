# The explicit right-polar blocks

## Abstract

Exact radical rotations for the active reverse source matrix.

Set s = sqrt(11), t = sqrt(10), D(l) = sqrt((l s + 3t)^2 + (s-t)^2), c(l) = (l s + 3t)/D(l), and k(l) = (s-t)/D(l). The two coupled blocks use l = 4 and l = 2. The remaining block is t times the matrix with diagonal 3 and off-diagonal -1. The active source matrix is Y diag(s,t,t,s,t,t)/62.

**Theorem 1.1 (The fixed radical unitary).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReversePolar.actual_unitary`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReversePolar.actual_unitary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both exact radical parameter pairs satisfy the unit-circle equation. The active matrix U therefore satisfies both complex unitary identities, and both sine parameters are strictly positive.

**Theorem 1.2 (A positive source polar product).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReversePolar.actual_polar_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReversePolar.actual_polar_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal active product M U is positive semidefinite. Each coupled block is symmetric with positive first diagonal entry and determinant (3l-1)s t. Unnormalized Hadamard columns reconstruct the complete six-dimensional product as a sum of positive congruences.

**Theorem 1.3 (A literal nonnegative SVD).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReversePolar.active_svd`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReversePolar.active_svd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Hermitian spectral decomposition of the positive product supplies two unitary factors and nonnegative singular values. Their source-ordered adjoints multiply to the explicit active rotation. This statement concerns the active block; its full source padding is a further identification.

**Theorem 1.4 (The fixed positive polynomial gap).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReversePolar.actual_polynomial_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReversePolar.actual_polynomial_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact radical parameters discharge every premise of the sum-of-squares positivity statement. This is an algebraic certificate; an actual decoder fidelity comparison additionally requires the canonical-purification and ordinary Petz identities.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/BurriReversePolar.active_svd`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReversePolar.actual_polar_positive`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReversePolar.actual_polynomial_gap`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReversePolar.actual_unitary`
- Dependency: [D5/S3/Quantum/Matrix/SpectralPower](../Matrix/SpectralPower.md)
- Dependency: [D5/S3/Quantum/Recovery/BurriReverseDecoder](BurriReverseDecoder.md)
