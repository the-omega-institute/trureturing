# ExactGramianSeries

## Abstract

Actual infinite Gramians: convergence, strict positivity, exact Stein equalities and finite-window remainders.

**Definition 1.1 (quadratic).**

Lean statement: `D5/S3/Observer/Hankel/ExactGramianSeries.quadratic`

*Formalization.* `D5/S3/Observer/Hankel/ExactGramianSeries.quadratic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The usual real matrix quadratic form on finite coordinate vectors.

**Theorem 1.2 (quadratic congruence).**

Lean statement: `D5/S3/Observer/Hankel/ExactGramianSeries.quadratic_congruence`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ExactGramianSeries.quadratic_congruence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proves the quadratic-form action of actual matrix congruence, including rectangular matrices.

**Theorem 1.3 (quadratic one).**

Lean statement: `D5/S3/Observer/Hankel/ExactGramianSeries.quadratic_one`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ExactGramianSeries.quadratic_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identifies identity-matrix energy with the existing Euclidean coordinate square sum.

**Theorem 1.4 (quadratic diagonal).**

Lean statement: `D5/S3/Observer/Hankel/ExactGramianSeries.quadratic_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ExactGramianSeries.quadratic_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identifies diagonal-matrix energy with the existing balanced Stein energy.

**Definition 1.5 (observation Term).**

Lean statement: `D5/S3/Observer/Hankel/ExactGramianSeries.observationTerm`

*Formalization.* `D5/S3/Observer/Hankel/ExactGramianSeries.observationTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The true output Gram term at each nonnegative time, formed from C times A to that power.

**Definition 1.6 (observation Gramian).**

Lean statement: `D5/S3/Observer/Hankel/ExactGramianSeries.observationGramian`

*Formalization.* `D5/S3/Observer/Hankel/ExactGramianSeries.observationGramian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The infinite undiscounted series of actual observation terms. Convergence is established separately.

**Definition 1.7 (control Gramian).**

Lean statement: `D5/S3/Observer/Hankel/ExactGramianSeries.controlGramian`

*Formalization.* `D5/S3/Observer/Hankel/ExactGramianSeries.controlGramian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Constructs the dual observation Gramian; a theorem identifies it with the standard reachability series.

**Theorem 1.8 (power square summable of bound).**

Lean statement: `D5/S3/Observer/Hankel/ExactGramianSeries.power_square_summable_of_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ExactGramianSeries.power_square_summable_of_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An exponential bound on powers implies square-summable powers. The single-step operator norm may exceed one.

**Theorem 1.9 (observation Term summable).**

Lean statement: `D5/S3/Observer/Hankel/ExactGramianSeries.observationTerm_summable`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ExactGramianSeries.observationTerm_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proves convergence in the matrix Euclidean operator norm using square-summable powers.

**Theorem 1.10 (adjoint power square summable).**

Lean statement: `D5/S3/Observer/Hankel/ExactGramianSeries.adjoint_power_square_summable`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ExactGramianSeries.adjoint_power_square_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proves the same power stability condition for the adjoint system.

**Theorem 1.11 (observation Gramian energy).**

Lean statement: `D5/S3/Observer/Hankel/ExactGramianSeries.observationGramian_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ExactGramianSeries.observationGramian_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quadratic form of the actual infinite series equals total actual future-output energy.

**Theorem 1.12 (observation energy summable).**

Lean statement: `D5/S3/Observer/Hankel/ExactGramianSeries.observation_energy_summable`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ExactGramianSeries.observation_energy_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proves summability of the future-output energy for every state.

**Theorem 1.13 (observation Gramian pos Semidef).**

Lean statement: `D5/S3/Observer/Hankel/ExactGramianSeries.observationGramian_posSemidef`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ExactGramianSeries.observationGramian_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual Gramian is positive semidefinite without assuming full observation.

**Theorem 1.14 (observation Gramian pos Def).**

Lean statement: `D5/S3/Observer/Hankel/ExactGramianSeries.observationGramian_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ExactGramianSeries.observationGramian_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Derives strict positivity from joint injectivity of actual future readouts. Gramian positivity is not an input.

**Theorem 1.15 (observation Gramian stein).**

Lean statement: `D5/S3/Observer/Hankel/ExactGramianSeries.observationGramian_stein`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ExactGramianSeries.observationGramian_stein` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Splits the convergent infinite series and proves the exact observability Stein equality.

**Theorem 1.16 (control Gramian stein).**

Lean statement: `D5/S3/Observer/Hankel/ExactGramianSeries.controlGramian_stein`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ExactGramianSeries.controlGramian_stein` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Derives the exact controllability Stein equality for the dual series.

**Theorem 1.17 (control Gramian series).**

Lean statement: `D5/S3/Observer/Hankel/ExactGramianSeries.controlGramian_series`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ExactGramianSeries.controlGramian_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identifies the dual definition with the usual sum of actual reachability blocks times their adjoints.

**Theorem 1.18 (control Gramian pos Def).**

Lean statement: `D5/S3/Observer/Hankel/ExactGramianSeries.controlGramian_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ExactGramianSeries.controlGramian_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Joint injectivity of all dual readouts implies positive definiteness of the actual control Gramian.

**Theorem 1.19 (observation Gramian eq existing).**

Lean statement: `D5/S3/Observer/Hankel/ExactGramianSeries.observationGramian_eq_existing`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ExactGramianSeries.observationGramian_eq_existing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identifies the matrix sum with the existing repository operator Gramian at discount one on Euclidean coordinates.

**Theorem 1.20 (observation Gramian finite remainder).**

Lean statement: `D5/S3/Observer/Hankel/ExactGramianSeries.observationGramian_finite_remainder`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ExactGramianSeries.observationGramian_finite_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Gives the exact finite-window remainder as terminal-state conjugation of the full Gramian.

## References

- Truth anchor: `D5/S3/Observer/Hankel/ExactGramianSeries.adjoint_power_square_summable`
- Truth anchor: `D5/S3/Observer/Hankel/ExactGramianSeries.controlGramian`
- Truth anchor: `D5/S3/Observer/Hankel/ExactGramianSeries.controlGramian_posDef`
- Truth anchor: `D5/S3/Observer/Hankel/ExactGramianSeries.controlGramian_series`
- Truth anchor: `D5/S3/Observer/Hankel/ExactGramianSeries.controlGramian_stein`
- Truth anchor: `D5/S3/Observer/Hankel/ExactGramianSeries.observationGramian`
- Truth anchor: `D5/S3/Observer/Hankel/ExactGramianSeries.observationGramian_energy`
- Truth anchor: `D5/S3/Observer/Hankel/ExactGramianSeries.observationGramian_eq_existing`
- Truth anchor: `D5/S3/Observer/Hankel/ExactGramianSeries.observationGramian_finite_remainder`
- Truth anchor: `D5/S3/Observer/Hankel/ExactGramianSeries.observationGramian_posDef`
- Truth anchor: `D5/S3/Observer/Hankel/ExactGramianSeries.observationGramian_posSemidef`
- Truth anchor: `D5/S3/Observer/Hankel/ExactGramianSeries.observationGramian_stein`
- Truth anchor: `D5/S3/Observer/Hankel/ExactGramianSeries.observationTerm`
- Truth anchor: `D5/S3/Observer/Hankel/ExactGramianSeries.observationTerm_summable`
- Truth anchor: `D5/S3/Observer/Hankel/ExactGramianSeries.observation_energy_summable`
- Truth anchor: `D5/S3/Observer/Hankel/ExactGramianSeries.power_square_summable_of_bound`
- Truth anchor: `D5/S3/Observer/Hankel/ExactGramianSeries.quadratic`
- Truth anchor: `D5/S3/Observer/Hankel/ExactGramianSeries.quadratic_congruence`
- Truth anchor: `D5/S3/Observer/Hankel/ExactGramianSeries.quadratic_diagonal`
- Truth anchor: `D5/S3/Observer/Hankel/ExactGramianSeries.quadratic_one`
- Dependency: [D5/S3/Observer/Hankel/BalancedSteinEnergy](BalancedSteinEnergy.md)
- Dependency: [D5/S3/Observer/Hankel/PositiveGramianBalancing](PositiveGramianBalancing.md)
- Dependency: [D5/S3/Observer/Linear/DiscountedObservabilityGramianPositivity](../Linear/DiscountedObservabilityGramianPositivity.md)
