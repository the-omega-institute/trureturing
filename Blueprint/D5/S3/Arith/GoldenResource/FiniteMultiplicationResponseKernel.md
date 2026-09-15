# Finite Multiplication Response Kernels

## Abstract

Finite Multiplication Response Kernels.

**Theorem 1.1 (Classification at a positive finite horizon).**

Lean statement: `D5/S3/Arith/GoldenResource/FiniteMultiplicationResponseKernel.eq_plus_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/FiniteMultiplicationResponseKernel.eq_plus_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a finite set of coordinates, a natural capacity on each coordinate, and a horizon of at least one. States are natural vectors bounded by these capacities. A multiplication letter increases its coordinate by one and fails at capacity. Successful words return the parity sign of the coordinate sum when every endpoint coordinate is at most one, and zero otherwise. Failure is distinct from every successful readout, including zero. Two states have equal responses to every word of length at most the horizon exactly when they are equal, or both are not squarefree and their remaining capacities agree after coordinatewise truncation at the horizon. Thus each squarefree state is a singleton, while truncated remaining capacity classifies the other states. Zero capacities and an empty coordinate set are allowed.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/FiniteMultiplicationResponseKernel.eq_plus_iff`
- Dependency: [D5/S0/Rewriting/GuardedBoxPaths](../../../S0/Rewriting/GuardedBoxPaths.md)
