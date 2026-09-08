# Single-State Balanced Truncation

## Abstract

Actual principal truncation inherits both Stein inequalities and satisfies finite-horizon two-sigma error bounds.

**Definition 1.1 (Keep).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationStep.keep`

*Formalization.* `D5/S3/Observer/Hankel/BalancedTruncationStep.keep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Retains the first n coordinates of an n+1 dimensional state.

**Definition 1.2 (Lift).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationStep.lift`

*Formalization.* `D5/S3/Observer/Hankel/BalancedTruncationStep.lift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Pads the retained state with a zero final coordinate.

**Definition 1.3 (Truncate a).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationStep.truncateA`

*Formalization.* `D5/S3/Observer/Hankel/BalancedTruncationStep.truncateA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Constructs the actual principal transition block by row and column restriction.

**Definition 1.4 (Truncate b).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationStep.truncateB`

*Formalization.* `D5/S3/Observer/Hankel/BalancedTruncationStep.truncateB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Constructs the actual retained input rows.

**Definition 1.5 (Truncate c).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationStep.truncateC`

*Formalization.* `D5/S3/Observer/Hankel/BalancedTruncationStep.truncateC` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Constructs the actual retained output columns.

**Theorem 1.6 (Lift last).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationStep.lift_last`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedTruncationStep.lift_last` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The padded coordinate is zero.

**Theorem 1.7 (Keep lift).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationStep.keep_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedTruncationStep.keep_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constructed projection and lift form a retraction.

**Theorem 1.8 (Keep add).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationStep.keep_add`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedTruncationStep.keep_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coordinate restriction preserves addition.

**Theorem 1.9 (Keep sub).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationStep.keep_sub`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedTruncationStep.keep_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coordinate restriction preserves subtraction.

**Theorem 1.10 (Keep smul).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationStep.keep_smul`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedTruncationStep.keep_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coordinate restriction preserves scalar multiplication.

**Definition 1.11 (Keep map).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationStep.keepMap`

*Formalization.* `D5/S3/Observer/Hankel/BalancedTruncationStep.keepMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Continuous linear coordinate projection, usable by the existing projected-realization interface.

**Definition 1.12 (Lift map).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationStep.liftMap`

*Formalization.* `D5/S3/Observer/Hankel/BalancedTruncationStep.liftMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Continuous linear zero-padding map, usable by the existing projected-realization interface.

**Theorem 1.13 (Keep mul lift).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationStep.keep_mul_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedTruncationStep.keep_mul_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The retained action on a lifted state is exactly the principal transition block.

**Theorem 1.14 (Keep mul input).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationStep.keep_mul_input`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedTruncationStep.keep_mul_input` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Projecting the input action gives exactly the retained input rows.

**Theorem 1.15 (Output mul lift).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationStep.output_mul_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedTruncationStep.output_mul_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reading a lifted state gives exactly the retained output columns.

**Theorem 1.16 (Truncated model is projected).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationStep.truncated_model_is_projected`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedTruncationStep.truncated_model_is_projected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identifies all three constructed matrix blocks with the existing P A J, P B and C J reduced maps. This is the direct downstream connection to ProjectedRealizationError.

**Theorem 1.17 (Energy split).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationStep.energy_split`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedTruncationStep.energy_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Splits a diagonal quadratic form into the retained energy and the final-coordinate energy.

**Theorem 1.18 (Energy lift).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationStep.energy_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedTruncationStep.energy_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Zero-padding contributes no final-coordinate energy.

**Theorem 1.19 (Truncate preserves stein).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationStep.truncate_preserves_stein`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedTruncationStep.truncate_preserves_stein` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Tests each full-system Stein inequality on a zero-padded vector and drops a nonnegative omitted-coordinate term. The resulting retained system satisfies inequalities; equality preservation is not asserted.

**Definition 1.20 (Truncation storage).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationStep.truncationStorage`

*Formalization.* `D5/S3/Observer/Hankel/BalancedTruncationStep.truncationStorage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Concrete balanced error storage, combining the difference state in the diagonal metric and the sum state in the inverse metric.

**Theorem 1.21 (Truncation storage nonneg).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationStep.truncationStorage_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedTruncationStep.truncationStorage_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive diagonal weights make the actual error storage nonnegative.

**Definition 1.22 (Discarded forcing).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationStep.discardedForcing`

*Formalization.* `D5/S3/Observer/Hankel/BalancedTruncationStep.discardedForcing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The omitted forcing is computed from the full matrices, the actual reduced state and the current input.

**Theorem 1.23 (Single step dissipation).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationStep.single_step_dissipation`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedTruncationStep.single_step_dissipation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expands both actual next states. The omitted-coordinate cross terms cancel between difference and sum storage, producing the coefficient four sigma squared and an additional nonnegative forcing term.

**Theorem 1.24 (Finite horizon dissipation).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationStep.finite_horizon_dissipation`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedTruncationStep.finite_horizon_dissipation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Inductively telescopes the single-step inequality along the two actual zero-initial trajectories. Terminal storage and omitted-forcing energy are retained. No contraction or limiting premise is used.

**Theorem 1.25 (Finite horizon output bound).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationStep.finite_horizon_output_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedTruncationStep.finite_horizon_output_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Drops the proved nonnegative storage and omitted-forcing terms to obtain the squared two-sigma output bound.

## References

- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationStep.discardedForcing`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationStep.energy_lift`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationStep.energy_split`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationStep.finite_horizon_dissipation`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationStep.finite_horizon_output_bound`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationStep.keep`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationStep.keepMap`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationStep.keep_add`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationStep.keep_lift`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationStep.keep_mul_input`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationStep.keep_mul_lift`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationStep.keep_smul`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationStep.keep_sub`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationStep.lift`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationStep.liftMap`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationStep.lift_last`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationStep.output_mul_lift`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationStep.single_step_dissipation`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationStep.truncateA`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationStep.truncateB`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationStep.truncateC`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationStep.truncate_preserves_stein`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationStep.truncated_model_is_projected`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationStep.truncationStorage`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationStep.truncationStorage_nonneg`
- Dependency: [D5/S3/Observer/Hankel/BalancedSteinEnergy](BalancedSteinEnergy.md)
