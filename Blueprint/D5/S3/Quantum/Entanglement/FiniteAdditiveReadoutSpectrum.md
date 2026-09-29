# Finite Additive Readout Spectrum

## Abstract

Finite additive readouts of one coherent source determine quotient blocks and flat marginals.

For finite additive commutative groups G, A and B, the two additive readouts alpha and beta have a jointly injective paired map. Every matrix here is computed from the source sum normalized by the square root of the source cardinality. The quotient is G modulo the sum of the readout kernels. The positive block weight is the product of their cardinalities divided by the source cardinality. Logarithms are natural logarithms.

**Theorem 1.1 (Exact eigenspaces and dimensions).**

Lean statement: `D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum.actual_eigenspaces`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum.actual_eigenspaces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On either side, a vector has eigenvalue equal to the positive block weight exactly when it lies in the range of that side's block-column matrix. The zero eigenspace is the kernel of its conjugate transpose. The positive eigenspaces have dimension equal to the quotient cardinality; the zero eigenspaces have the ambient dimension minus that cardinality.

**Theorem 1.2 (Ranks and flat marginal spectra).**

Lean statement: `D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum.actual_flat_reductions`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum.actual_flat_reductions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The kernels intersect only at zero, their sum has the product cardinality, and the source cardinality is that product times the quotient cardinality. The block weight is the reciprocal quotient cardinality. Both actual marginals have trace one and rank equal to the quotient cardinality, as does the actual coefficient matrix. Their positive eigenvalues equal the block weight with that multiplicity; all remaining eigenvalues are zero. The von Neumann entropy of either actual marginal is the logarithm of the quotient cardinality, equal to the source-cardinality logarithm minus the two kernel-cardinality logarithms. The actual coefficient map between Euclidean spaces has the square root of the block weight as each positive singular value, repeated the quotient cardinality times, with every subsequent singular value zero.

**Theorem 1.3 (Normalized joint pure state).**

Lean statement: `D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum.actual_joint_state`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum.actual_joint_state` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The outer product of the actual coefficients is positive semidefinite and Hermitian, has trace and rank one, and is idempotent. The coefficient norm square is one. The sum of the actual source basis kets equals the coefficient vector coordinate by coordinate, and equals the sum of the products of the normalized block vectors scaled by the square root of the block weight.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum.actual_eigenspaces`
- Truth anchor: `D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum.actual_flat_reductions`
- Truth anchor: `D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum.actual_joint_state`
- Dependency: [D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutBlocks](FiniteAdditiveReadoutBlocks.md)
