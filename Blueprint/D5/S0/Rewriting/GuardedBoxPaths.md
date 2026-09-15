# Guarded Box Paths

## Abstract

Guarded Box Paths.

**Theorem 1.1 (Signed coordinate displacement).**

Lean statement: `D5/S0/Rewriting/GuardedBoxPaths.endpoint_counts`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/GuardedBoxPaths.endpoint_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A unit instruction increases one natural coordinate below its capacity, or decreases one positive coordinate. Evaluation proceeds from left to right and fails when a guard fails. For any successfully evaluated word, the integer difference between final and initial values of each coordinate equals its number of increases minus its number of decreases.

**Theorem 1.2 (Coordinate lower bounds and equality).**

Lean statement: `D5/S0/Rewriting/GuardedBoxPaths.path_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/GuardedBoxPaths.path_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite coordinate set, a legal word starts inside the capacity box and every instruction passes its guard. Each coordinate receives at least the absolute difference between its endpoint values in instructions. The word length is the sum of the coordinate counts and is at least the sum of the absolute differences. Equality holds exactly when every instruction on each coordinate has the direction of its endpoint difference and the coordinate count equals that absolute difference. A coordinate with equal endpoints then receives no instructions. The argument uses the signed count identity without deleting or reordering instructions.

## References

- Truth anchor: `D5/S0/Rewriting/GuardedBoxPaths.endpoint_counts`
- Truth anchor: `D5/S0/Rewriting/GuardedBoxPaths.path_lower_bound`
