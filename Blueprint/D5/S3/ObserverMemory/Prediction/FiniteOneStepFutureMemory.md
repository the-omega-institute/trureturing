# Finite One-Step Future Memory

## Abstract

All genuine finite-state probability laws determine one-step future expectations exactly at the one-step pullback closure, with a sharp same-V quotient bound.

**Theorem 1.1 (All-laws one-step closure and minimal quotient memory).**

$$oneStepDetermines iff oneStepFutureClosed and quotientLowerBound and closureAttainment.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiniteOneStepFutureMemory.finite_one_step_future_memory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state domain is finite, the action type is arbitrary, and each action is a fixed deterministic transition. V is the retained observation space and contains every constant function.

For every pair of genuine nonnegative normalized laws, agreement on all expectations from W implies agreement on every expectation of a pullback of an element of V. This statistical condition is equivalent to retaining V and containing all one-step pullbacks.

The closure is V plus the span of those pullbacks. Every feasible W has at least the closure's quotient dimension over the same embedded V, and the closure itself is feasible and attains equality. Empty and singleton state domains and an empty action family remain allowed; the statement is one-step and does not assert recursive invariant closure.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiniteOneStepFutureMemory.finite_one_step_future_memory`
