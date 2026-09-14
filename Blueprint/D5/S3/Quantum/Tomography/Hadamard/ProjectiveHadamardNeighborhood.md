# Projective Hadamard complex neighborhoods

## Abstract

Projective ratios provide one complex domain across changes of anchor, with a scale-independent residual differential.

**Definition 1.1 (phaseRatioDomain).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/ProjectiveHadamardNeighborhood.phaseRatioDomain`

*Formalization.* `D5/S3/Quantum/Tomography/Hadamard/ProjectiveHadamardNeighborhood.phaseRatioDomain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A fixed-width open domain defined by all pairwise phase-modulus ratios. It contains the entire unit phase torus when R is greater than one.

**Definition 1.2 (projectiveHadamardResidual).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/ProjectiveHadamardNeighborhood.projectiveHadamardResidual`

*Formalization.* `D5/S3/Quantum/Tomography/Hadamard/ProjectiveHadamardNeighborhood.projectiveHadamardResidual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The nonzero-phase Laurent coordinates of the existing paired residual. The matrix is fixed; conjugation is only on its coefficients.

**Theorem 1.3 (projective_reanchoring_preserves_domain_and_residual).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/ProjectiveHadamardNeighborhood.projective_reanchoring_preserves_domain_and_residual`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/Hadamard/ProjectiveHadamardNeighborhood.projective_reanchoring_preserves_domain_and_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every choice of a nonzero anchor preserves the same ratio domain and all actual residual values. The new anchor is exactly one and all coordinate moduli remain between 1/R and R. Successive anchor changes do not accumulate a width loss.

**Theorem 1.4 (phase_ratio_domain_open_torus_and_gauges).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/ProjectiveHadamardNeighborhood.phase_ratio_domain_open_torus_and_gauges`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/Hadamard/ProjectiveHadamardNeighborhood.phase_ratio_domain_open_torus_and_gauges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The domain is open and contains all unit-phase inputs. Its defining condition is unchanged by nonzero common scaling, permutations, unit coordinate prefactors, and conjugation. Only domain invariance is claimed for the latter transformations; a fixed matrix residual need not be invariant under independent row phases.

**Theorem 1.5 (projective_residual_hasFDerivAt_and_scaled_bound).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/ProjectiveHadamardNeighborhood.projective_residual_hasFDerivAt_and_scaled_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/Hadamard/ProjectiveHadamardNeighborhood.projective_residual_hasFDerivAt_and_scaled_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit complex Frechet derivative is derived from the actual Laurent residual. Each Euler-scaled Jacobian entry w_k J_ak has norm at most 10 R M^2 in dimension six. The self-index term cancels before the remaining five terms are bounded. This is not an inverse-Jacobian estimate or an automatic bound on a differently parameterized Cayley Newton map.

**Theorem 1.6 (paired_cayley_residual_eq_projective_readout).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/ProjectiveHadamardNeighborhood.paired_cayley_residual_eq_projective_readout`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/Hadamard/ProjectiveHadamardNeighborhood.paired_cayley_residual_eq_projective_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On every pole-free Cayley chart with unit prefactors, the new coordinate expression equals the already owned pairedCayleyResidual. The equality holds on complex coordinates, not only on the real slice.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/ProjectiveHadamardNeighborhood.paired_cayley_residual_eq_projective_readout`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/ProjectiveHadamardNeighborhood.phaseRatioDomain`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/ProjectiveHadamardNeighborhood.phase_ratio_domain_open_torus_and_gauges`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/ProjectiveHadamardNeighborhood.projectiveHadamardResidual`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/ProjectiveHadamardNeighborhood.projective_reanchoring_preserves_domain_and_residual`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/ProjectiveHadamardNeighborhood.projective_residual_hasFDerivAt_and_scaled_bound`
- Dependency: [D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard](../HolomorphicCayleyHadamard.md)
