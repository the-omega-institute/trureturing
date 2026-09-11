# A Twenty-State Finite-Prefix Barrier

## Abstract

An explicit twenty-state table fits all original power indices below 367 and first fails at 367. Dictionaries confined to that prefix cannot refute every twenty-state candidate.

**Definition 1.1 (stateType).**

Lean statement: `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.stateType`

*Formalization.* `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.stateType` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The thirteen previous-zero rows and seven previous-one rows.

**Definition 1.2 (zeroTarget).**

Lean statement: `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.zeroTarget`

*Formalization.* `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.zeroTarget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Zero successors of the explicit finite-prefix witness.

**Definition 1.3 (oneTarget).**

Lean statement: `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.oneTarget`

*Formalization.* `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.oneTarget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One successors; unused entries remain hidden behind the type guard.

**Definition 1.4 (output).**

Lean statement: `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.output`

*Formalization.* `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.output` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The output is always a base-four digit.

**Definition 1.5 (step).**

Lean statement: `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.step`

*Formalization.* `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every legal symbol has a successor; consecutive ones remain undefined.

**Definition 1.6 (machine).**

Lean statement: `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.machine`

*Formalization.* `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.machine` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A concrete machine in the same candidate class as the original problem.

**Theorem 1.7 (correct_before_367).**

Lean statement: `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.correct_before_367`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.correct_before_367` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every original power input with index below 367 is computed correctly.

**Theorem 1.8 (output_at_367).**

Lean statement: `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.output_at_367`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.output_at_367` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At index 367 the concrete twenty-state table emits one.

**Theorem 1.9 (true_digit_at_367).**

Lean statement: `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.true_digit_at_367`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.true_digit_at_367` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original exact arithmetic oracle has digit zero at index 367.

**Theorem 1.10 (fails_at_367).**

Lean statement: `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.fails_at_367`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.fails_at_367` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This finite-prefix witness is not a solution of the infinite problem.

**Theorem 1.11 (no_earlier_failure).**

Lean statement: `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.no_earlier_failure`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.no_earlier_failure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every failure of this witness is at least the explicitly attained index.

**Theorem 1.12 (initial_anchors).**

Lean statement: `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.initial_anchors`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.initial_anchors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both published initial anchors hold, including the leading-zero loop.

**Theorem 1.13 (every_subprefix_has_twenty_state_witness).**

Lean statement: `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.every_subprefix_has_twenty_state_witness`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.every_subprefix_has_twenty_state_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every collection of observations confined to indices below 367 has a 20-state witness. This includes the original 79 rows and the 144 gap4 rows. The indices may repeat and the collection may be described by any index type.

## References

- Truth anchor: `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.correct_before_367`
- Truth anchor: `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.every_subprefix_has_twenty_state_witness`
- Truth anchor: `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.fails_at_367`
- Truth anchor: `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.initial_anchors`
- Truth anchor: `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.machine`
- Truth anchor: `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.no_earlier_failure`
- Truth anchor: `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.oneTarget`
- Truth anchor: `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.output`
- Truth anchor: `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.output_at_367`
- Truth anchor: `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.stateType`
- Truth anchor: `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.step`
- Truth anchor: `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.true_digit_at_367`
- Truth anchor: `D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.zeroTarget`
- Dependency: [D5/S1/Digit/GoldenBase4DenseInput](GoldenBase4DenseInput.md)
