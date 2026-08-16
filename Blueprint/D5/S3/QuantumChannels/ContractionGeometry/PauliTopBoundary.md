# The Pauli Top Boundary Has Zero Volume

## Abstract

The top boundary of three Pauli contraction parameters is a null set for volume.

**Theorem 1.1 (The top boundary has zero volume).**

$$volume(pauliTopBoundary) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/ContractionGeometry/PauliTopBoundary.pauli_top_boundary_volume_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Represent the three diagonal Pauli contraction coefficients by a real triple t with the sup norm, and define its top value as the square of that norm. The locus where the top value equals one is exactly the unit sup-norm sphere, equivalently the boundary of the closed unit ball.

Mathlib proves that the boundary of a convex set in a finite-dimensional real normed space has zero measure for every additive Haar measure. Applying that theorem to the closed unit ball gives zero volume for the Pauli top boundary. No claim is made here about the other ordering, counterexample, or qubit-channel clauses in the source atom.

## References

- Truth anchor: `D5/S3/QuantumChannels/ContractionGeometry/PauliTopBoundary.pauli_top_boundary_volume_zero`
