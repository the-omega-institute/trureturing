# Ordered Stable Balanced Truncation

## Abstract

The same constructed largest-singular-weight reduced model is strictly internally stable and obeys both tail-sum error bounds.

**Theorem 1.1 (Transport every future readout).**

Lean statement: `D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.balanced_future_readout`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.balanced_future_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proves the complete matrix readout identity through all powers of the actual balanced transition.

**Theorem 1.2 (Inherited full observation).**

Lean statement: `D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.balanced_full_observable`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.balanced_full_observable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proves joint readout injectivity for the full balanced realization using original-system observability and both inverse coordinate maps. Reduced observability is not assumed.

**Definition 1.3 (Construct ordered system coordinates).**

Lean statement: `D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.orderedSystemCoordinates`

*Formalization.* `D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.orderedSystemCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Constructs actual infinite Gramians and balancing maps, then applies the same descending permutation to the weights and state coordinates.

**Theorem 1.4 (Ordered genuine Hankel singular modes).**

Lean statement: `D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.ordered_hankel_schmidt`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.ordered_hankel_schmidt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sorted positive weights retain the actual infinite Hankel orthonormal modes, both singular-vector equations, complete expansion and kernel characterization.

**Theorem 1.5 (Strict stability of the actual ordered cut).**

Lean statement: `D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.ordered_reduction_spectrum_lt_one`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.ordered_reduction_spectrum_lt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Derives all complex poles of the actual largest-weight prefix model inside the open unit disk from original-system hypotheses. Repeated weights and empty cuts are included without an assumed gap.

**Theorem 1.6 (Ordered finite-window tail bound).**

Lean statement: `D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.ordered_reduction_window_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.ordered_reduction_window_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identical constructed ordered model satisfies the original-system finite-window error bound with the discarded singular tail.

**Theorem 1.7 (Ordered infinite-energy tail bound).**

Lean statement: `D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.ordered_reduction_l2_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.ordered_reduction_l2_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the identical model, proves error-energy summability and the infinite-time tail-sum error estimate.

**Theorem 1.8 (Single-model ordered stable reduction theorem).**

Lean statement: `D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.ordered_stable_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.ordered_stable_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One construction simultaneously retains the largest weights, is strictly stable in the standard complex spectrum, and satisfies both finite-window and whole-half-line error bounds. All clauses reference the same state, input and output matrices.

## References

- Truth anchor: `D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.balanced_full_observable`
- Truth anchor: `D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.balanced_future_readout`
- Truth anchor: `D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.orderedSystemCoordinates`
- Truth anchor: `D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.ordered_hankel_schmidt`
- Truth anchor: `D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.ordered_reduction_l2_bound`
- Truth anchor: `D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.ordered_reduction_spectrum_lt_one`
- Truth anchor: `D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.ordered_reduction_window_bound`
- Truth anchor: `D5/S3/Observer/Hankel/OrderedStableBalancedTruncation.ordered_stable_reduction`
- Dependency: [D5/S3/Observer/Hankel/DiscreteSteinCompressionStability](DiscreteSteinCompressionStability.md)
- Dependency: [D5/S3/Observer/Hankel/OrderedBalancedCoordinates](OrderedBalancedCoordinates.md)
