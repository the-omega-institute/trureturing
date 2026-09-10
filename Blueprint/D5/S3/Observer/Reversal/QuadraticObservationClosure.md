# Quadratic Observation Closure

## Abstract

Quadratic observed dynamics closes exactly when its hidden linear, hidden quadratic, and mixed terms vanish.

**Definition 1.1 (vectorField).**

Lean statement: `D5/S3/Observer/Reversal/QuadraticObservationClosure.vectorField`

*Formalization.* `D5/S3/Observer/Reversal/QuadraticObservationClosure.vectorField` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Linear drift minus the diagonal of a genuine bilinear map.

**Theorem 1.2 (observed increment).**

Lean statement: `D5/S3/Observer/Reversal/QuadraticObservationClosure.observed_increment`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Reversal/QuadraticObservationClosure.observed_increment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact observed increment, including the hidden self-interaction.

**Theorem 1.3 (quadratic closure iff).**

Lean statement: `D5/S3/Observer/Reversal/QuadraticObservationClosure.quadratic_closure_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Reversal/QuadraticObservationClosure.quadratic_closure_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A complete necessary and sufficient condition for exact Markovian closure of a quadratic vector field under a linear projection.

**Theorem 1.4 (quadratic fiber criterion).**

Lean statement: `D5/S3/Observer/Reversal/QuadraticObservationClosure.quadratic_fiber_criterion`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Reversal/QuadraticObservationClosure.quadratic_fiber_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient criterion is equivalent to the pre-existing answerability condition on all pairs in every observation fiber.

**Theorem 1.5 (same visible negation).**

Lean statement: `D5/S3/Observer/Reversal/QuadraticObservationClosure.same_visible_negation`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Reversal/QuadraticObservationClosure.same_visible_negation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Full and visible-only reversal have the same observed state.

**Theorem 1.6 (reversal acceleration gap).**

Lean statement: `D5/S3/Observer/Reversal/QuadraticObservationClosure.reversal_acceleration_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Reversal/QuadraticObservationClosure.reversal_acceleration_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The surviving mixed term is the exact difference between the two observed accelerations. Linear hidden drift is the only extra hypothesis.

## References

- Truth anchor: `D5/S3/Observer/Reversal/QuadraticObservationClosure.observed_increment`
- Truth anchor: `D5/S3/Observer/Reversal/QuadraticObservationClosure.quadratic_closure_iff`
- Truth anchor: `D5/S3/Observer/Reversal/QuadraticObservationClosure.quadratic_fiber_criterion`
- Truth anchor: `D5/S3/Observer/Reversal/QuadraticObservationClosure.reversal_acceleration_gap`
- Truth anchor: `D5/S3/Observer/Reversal/QuadraticObservationClosure.same_visible_negation`
- Truth anchor: `D5/S3/Observer/Reversal/QuadraticObservationClosure.vectorField`
- Dependency: [D5/S0/Rewriting/Quotients/AnswerabilityCriterion](../../../S0/Rewriting/Quotients/AnswerabilityCriterion.md)
