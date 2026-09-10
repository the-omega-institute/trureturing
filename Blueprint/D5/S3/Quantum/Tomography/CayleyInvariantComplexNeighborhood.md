# A chart-invariant complex neighborhood

## Abstract

One open pole-free complex domain works at every subdivision depth and for every fixed matrix type.

**Definition 1.1 (The common domain).**

Lean statement: `D5/S3/Quantum/Tomography/CayleyInvariantComplexNeighborhood.cayleyNeighborhood`

*Formalization.* `D5/S3/Quantum/Tomography/CayleyInvariantComplexNeighborhood.cayleyNeighborhood` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inequality 10 abs(Im z) < 3(1+normSq z) defines the Cayley pullback of the annulus with radii one-half and two.

**Theorem 1.2 (Open real neighborhood with quantitative pole separation).**

Lean statement: `D5/S3/Quantum/Tomography/CayleyInvariantComplexNeighborhood.cayley_neighborhood_open_real_and_poles`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/CayleyInvariantComplexNeighborhood.cayley_neighborhood_open_real_and_poles` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The domain is open and contains the real axis. Both denominator squared norms exceed two-fifths.

**Theorem 1.3 (The same domain survives signed reciprocal transport).**

Lean statement: `D5/S3/Quantum/Tomography/CayleyInvariantComplexNeighborhood.cayley_neighborhood_chart_invariance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/CayleyInvariantComplexNeighborhood.cayley_neighborhood_chart_invariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Negation, conjugation and guarded negative reciprocal transport preserve exactly the same domain. Reciprocal transport is used only away from zero; no depth-dependent radius shrinkage is introduced.

**Theorem 1.4 (Uniform phase bounds).**

Lean statement: `D5/S3/Quantum/Tomography/CayleyInvariantComplexNeighborhood.cayley_neighborhood_phase_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/CayleyInvariantComplexNeighborhood.cayley_neighborhood_phase_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every unit-prefactor Cayley phase has squared norm strictly between one-fourth and four, independently of the sign or quarter-turn chart.

**Theorem 1.5 (Uniform actual complex Jacobian bound).**

Lean statement: `D5/S3/Quantum/Tomography/CayleyInvariantComplexNeighborhood.paired_cayley_jacobian_uniform_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/CayleyInvariantComplexNeighborhood.paired_cayley_jacobian_uniform_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If matrix coefficients have norm at most M, each Jacobian entry has norm at most 20 d M squared. In order six with unit entries the bound is 120. Gauge fixing and outcome deletion remove rows or columns only.

**Theorem 1.6 (Exact signed reciprocal phase identity).**

Lean statement: `D5/S3/Quantum/Tomography/CayleyInvariantComplexNeighborhood.cayley_phase_reciprocal_transition`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/CayleyInvariantComplexNeighborhood.cayley_phase_reciprocal_transition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The negative reciprocal coordinate change is compensated by negating the phase prefactor. The coordinate must be nonzero and in the common domain.

**Theorem 1.7 (Holomorphy persists under every certified restriction).**

Lean statement: `D5/S3/Quantum/Tomography/CayleyInvariantComplexNeighborhood.paired_residual_holomorphic_on_every_restriction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/CayleyInvariantComplexNeighborhood.paired_residual_holomorphic_on_every_restriction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any family of regions contained in the common coordinate domain inherits holomorphy of the actual residual. This is restriction stability. Boolean pruning and min/max are not holomorphic maps, and Newton self-invariance requires its separate quantitative budget.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/CayleyInvariantComplexNeighborhood.cayleyNeighborhood`
- Truth anchor: `D5/S3/Quantum/Tomography/CayleyInvariantComplexNeighborhood.cayley_neighborhood_chart_invariance`
- Truth anchor: `D5/S3/Quantum/Tomography/CayleyInvariantComplexNeighborhood.cayley_neighborhood_open_real_and_poles`
- Truth anchor: `D5/S3/Quantum/Tomography/CayleyInvariantComplexNeighborhood.cayley_neighborhood_phase_bounds`
- Truth anchor: `D5/S3/Quantum/Tomography/CayleyInvariantComplexNeighborhood.cayley_phase_reciprocal_transition`
- Truth anchor: `D5/S3/Quantum/Tomography/CayleyInvariantComplexNeighborhood.paired_cayley_jacobian_uniform_bound`
- Truth anchor: `D5/S3/Quantum/Tomography/CayleyInvariantComplexNeighborhood.paired_residual_holomorphic_on_every_restriction`
- Dependency: [D5/S3/Quantum/Tomography/HolomorphicCayleyHadamard](HolomorphicCayleyHadamard.md)
