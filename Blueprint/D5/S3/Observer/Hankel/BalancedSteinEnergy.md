# Diagonal Stein Energy Duality

## Abstract

A diagonal reachability Stein inequality yields inverse-storage input-energy dissipativity.

**Definition 1.1 (Energy).**

Lean statement: `D5/S3/Observer/Hankel/BalancedSteinEnergy.energy`

*Formalization.* `D5/S3/Observer/Hankel/BalancedSteinEnergy.energy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Quadratic form of a diagonal real matrix. Positivity is supplied separately and then used to prove nonnegative storage.

**Definition 1.2 (Square sum).**

Lean statement: `D5/S3/Observer/Hankel/BalancedSteinEnergy.squareSum`

*Formalization.* `D5/S3/Observer/Hankel/BalancedSteinEnergy.squareSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Euclidean squared size of a finite coordinate vector. This definition does not use the default Pi sup norm.

**Definition 1.3 (Matrix map).**

Lean statement: `D5/S3/Observer/Hankel/BalancedSteinEnergy.matrixMap`

*Formalization.* `D5/S3/Observer/Hankel/BalancedSteinEnergy.matrixMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reuses Mathlib matrix multiplication and the finite-dimensional linear-to-continuous-linear equivalence.

**Theorem 1.4 (Matrix map apply).**

Lean statement: `D5/S3/Observer/Hankel/BalancedSteinEnergy.matrixMap_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedSteinEnergy.matrixMap_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The continuous linear adapter acts by the original matrix-vector multiplication.

**Definition 1.5 (Matrix state).**

Lean statement: `D5/S3/Observer/Hankel/BalancedSteinEnergy.matrixState`

*Formalization.* `D5/S3/Observer/Hankel/BalancedSteinEnergy.matrixState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reuses the zero-initial forced recurrence already owned by ProjectedRealizationError.

**Definition 1.6 (Matrix response).**

Lean statement: `D5/S3/Observer/Hankel/BalancedSteinEnergy.matrixResponse`

*Formalization.* `D5/S3/Observer/Hankel/BalancedSteinEnergy.matrixResponse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Output of the actual matrix recurrence with zero initial state and no direct feedthrough term.

**Theorem 1.7 (Matrix state zero).**

Lean statement: `D5/S3/Observer/Hankel/BalancedSteinEnergy.matrixState_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedSteinEnergy.matrixState_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reused state constructor has zero initial state.

**Theorem 1.8 (Matrix state succ).**

Lean statement: `D5/S3/Observer/Hankel/BalancedSteinEnergy.matrixState_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedSteinEnergy.matrixState_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reused state constructor advances by the supplied transition and input matrices.

**Definition 1.9 (Observability stein).**

Lean statement: `D5/S3/Observer/Hankel/BalancedSteinEnergy.ObservabilityStein`

*Formalization.* `D5/S3/Observer/Hankel/BalancedSteinEnergy.ObservabilityStein` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The standard diagonal observability Stein inequality, quantified over every real state.

**Definition 1.10 (Reachability stein).**

Lean statement: `D5/S3/Observer/Hankel/BalancedSteinEnergy.ReachabilityStein`

*Formalization.* `D5/S3/Observer/Hankel/BalancedSteinEnergy.ReachabilityStein` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The standard diagonal reachability Stein inequality, quantified over every real dual state. An inverse-storage gain bound is not included as a premise.

**Definition 1.11 (Balanced stein).**

Lean statement: `D5/S3/Observer/Hankel/BalancedSteinEnergy.BalancedStein`

*Formalization.* `D5/S3/Observer/Hankel/BalancedSteinEnergy.BalancedStein` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A positive common diagonal satisfying both Stein inequalities. These data need not already be identified as the exact Gramians of a stable minimal system.

**Theorem 1.12 (Energy zero).**

Lean statement: `D5/S3/Observer/Hankel/BalancedSteinEnergy.energy_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedSteinEnergy.energy_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal quadratic form vanishes on the zero state.

**Theorem 1.13 (Square sum zero).**

Lean statement: `D5/S3/Observer/Hankel/BalancedSteinEnergy.squareSum_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedSteinEnergy.squareSum_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Zero coordinates have zero Euclidean squared size.

**Theorem 1.14 (Energy nonneg).**

Lean statement: `D5/S3/Observer/Hankel/BalancedSteinEnergy.energy_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedSteinEnergy.energy_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonnegative diagonal weights give nonnegative energy.

**Theorem 1.15 (Square sum nonneg).**

Lean statement: `D5/S3/Observer/Hankel/BalancedSteinEnergy.squareSum_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedSteinEnergy.squareSum_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite sum of real coordinate squares is nonnegative.

**Theorem 1.16 (Square sum smul).**

Lean statement: `D5/S3/Observer/Hankel/BalancedSteinEnergy.squareSum_smul`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedSteinEnergy.squareSum_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Scalar multiplication rescales Euclidean squared size by the square of the scalar.

**Theorem 1.17 (Inverse energy step).**

Lean statement: `D5/S3/Observer/Hankel/BalancedSteinEnergy.inverse_energy_step`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedSteinEnergy.inverse_energy_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Weighted Young inequalities and transposed matrix pairing derive inverse-diagonal dissipativity from the actual reachability Stein inequality. No gain or inverse-energy conclusion is assumed.

## References

- Truth anchor: `D5/S3/Observer/Hankel/BalancedSteinEnergy.BalancedStein`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedSteinEnergy.ObservabilityStein`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedSteinEnergy.ReachabilityStein`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedSteinEnergy.energy`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedSteinEnergy.energy_nonneg`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedSteinEnergy.energy_zero`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedSteinEnergy.inverse_energy_step`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedSteinEnergy.matrixMap`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedSteinEnergy.matrixMap_apply`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedSteinEnergy.matrixResponse`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedSteinEnergy.matrixState`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedSteinEnergy.matrixState_succ`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedSteinEnergy.matrixState_zero`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedSteinEnergy.squareSum`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedSteinEnergy.squareSum_nonneg`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedSteinEnergy.squareSum_smul`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedSteinEnergy.squareSum_zero`
- Dependency: [D5/S3/Observer/Hankel/ProjectedRealizationError](ProjectedRealizationError.md)
