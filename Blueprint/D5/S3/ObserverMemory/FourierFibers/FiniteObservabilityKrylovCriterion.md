# Finite Observability Krylov Criterion

## Abstract

A finite time window is faithful exactly when its existing observable Krylov space fills the carrier.

**Theorem 1.1 (Trivial hidden kernel equals full Krylov span).**

$$\forall E, r, d, \operatorname{inf}_{t \le d} \operatorname{ker}(r \circ E^{t}) = bot \iff \operatorname{observableKrylov}(E, r, d) = top.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FourierFibers/FiniteObservabilityKrylovCriterion.finite_hidden_kernel_trivial_iff_observable_krylov_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite common kernel of all delayed readouts is trivial exactly when the observable Krylov subspace is the whole finite-dimensional carrier.

This node reuses Trueturning's frozen orthogonal-duality theorem and Mathlib's orthogonal-complement criterion instead of introducing a parallel observability theory.

## References

- Truth anchor: `D5/S3/ObserverMemory/FourierFibers/FiniteObservabilityKrylovCriterion.finite_hidden_kernel_trivial_iff_observable_krylov_top`
- Dependency: [D5/S3/ObserverMemory/Dynamics/FiniteObservabilityOrthogonalDuality](../Dynamics/FiniteObservabilityOrthogonalDuality.md)
