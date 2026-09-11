# Holomorphic Cayley Hadamard residuals

## Abstract

A paired rational complexification recovers the actual real squared-modulus residual and exposes its complex Jacobian.

**Definition 1.1 (cayleyPhase).**

Lean statement: `D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.cayleyPhase`

*Formalization.* `D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.cayleyPhase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complex rational Cayley coordinate with a fixed phase prefactor.

**Definition 1.2 (pairedCayleyResidual).**

Lean statement: `D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.pairedCayleyResidual`

*Formalization.* `D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.pairedCayleyResidual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two analytic factors use fixed conjugated matrix coefficients and reciprocal phase companions. Complex normSq is not analytically continued.

**Definition 1.3 (pairedCayleyJacobian).**

Lean statement: `D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.pairedCayleyJacobian`

*Formalization.* `D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.pairedCayleyJacobian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Rows are outcomes and columns are phase coordinates. The reciprocal factor contributes the negative second term.

**Theorem 1.4 (paired cayley residual hasFDerivAt).**

Lean statement: `D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.paired_cayley_residual_hasFDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.paired_cayley_residual_hasFDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete complex Frechet derivative is the continuous linear map represented by the displayed Jacobian. Both denominators must be nonzero; matrix H is fixed.

**Definition 1.5 (dephasedCayleyResidual).**

Lean statement: `D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.dephasedCayleyResidual`

*Formalization.* `D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.dephasedCayleyResidual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fix phase zero to one and omit outcome five, leaving a square five-variable system. The sixth residual remains minus the sum of the five retained residuals; a six-outcome sublevel additionally bounds that sum.

**Theorem 1.6 (dephased cayley residual hasFDerivAt).**

Lean statement: `D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.dephased_cayley_residual_hasFDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.dephased_cayley_residual_hasFDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual five-by-five derivative is obtained by fixing coordinate zero and retaining the first five outcomes. No invertibility premise or conclusion is smuggled in.

**Theorem 1.7 (paired cayley residual on real).**

Lean statement: `D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.paired_cayley_residual_on_real`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.paired_cayley_residual_on_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real phase coordinates the holomorphic paired residual equals the real norm-square measurement residual as a complex number. Arbitrary fixed complex chart phases are allowed.

**Theorem 1.8 (paired cayley residual sum zero).**

Lean statement: `D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.paired_cayley_residual_sum_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.paired_cayley_residual_sum_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For scaled-unitary H and unit phase prefactors, the sum of all complex residuals is exactly zero throughout the pole-free domain. Matrix multiplication proves conservation without an identity-theorem oracle.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.cayleyPhase`
- Truth anchor: `D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.dephasedCayleyResidual`
- Truth anchor: `D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.dephased_cayley_residual_hasFDerivAt`
- Truth anchor: `D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.pairedCayleyJacobian`
- Truth anchor: `D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.pairedCayleyResidual`
- Truth anchor: `D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.paired_cayley_residual_hasFDerivAt`
- Truth anchor: `D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.paired_cayley_residual_on_real`
- Truth anchor: `D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard.paired_cayley_residual_sum_zero`
