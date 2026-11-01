# Vanishing phase error and unique ergodicity

## Abstract

Unique ergodicity of the actual recognizable balanced factorial subshift.

**Theorem 1.1 (A quantitative comparison).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedUniqueErgodic.window_event_measure_difference_le`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedUniqueErgodic.window_event_measure_difference_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any two invariant probabilities on the actual balanced subshift, their masses on an event determined by a signed window of length r differ by at most r/3^n at every level n. Both masses lie in the same good-phase counting interval, and its width is bounded by the exact disagreement identity for the literal balanced words.

**Theorem 1.2 (Equality on finite observations).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedUniqueErgodic.window_event_measure_eq`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedUniqueErgodic.window_event_measure_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The geometric error tends to zero as the phase level tends to infinity. The two invariant probabilities therefore give exactly the same mass to every event determined by a finite signed window. The window itself is fixed while the recognizing tile height grows.

**Theorem 1.3 (Equality of the actual measures).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedUniqueErgodic.balanced_invariant_probability_unique`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedUniqueErgodic.balanced_invariant_probability_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any finite set of integer coordinates fits inside a finite signed interval. Every measurable cylinder in the ambient full shift therefore pulls back to a finite-window event. Push both probabilities through the measurable subtype inclusion, apply Mathlib's existing generating cylinder pi-system to identify the ambient measures, and use injectivity of the pushforward along the measurable embedding to recover equality on actual balanced points.

**Theorem 1.4 (The unique invariant probability).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedUniqueErgodic.balanced_unique_ergodic`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedUniqueErgodic.balanced_unique_ergodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Combining actual invariant-probability existence with uniqueness proves that exactly one probability measure on the balanced point space is preserved by the one-step shift. This establishes unique ergodicity of this concrete compact subshift. Minimality, Toeplitz points, finite-group cocycles, and claims about a published open problem belong to their separate proof steps.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedUniqueErgodic.balanced_invariant_probability_unique`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedUniqueErgodic.balanced_unique_ergodic`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedUniqueErgodic.window_event_measure_difference_le`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedUniqueErgodic.window_event_measure_eq`
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMeasures](BalancedMeasures.md)
