# Completion Point Pullback

## Abstract

Completion points pull back exactly along a change of state representation.

**Theorem 1.1 (Pointwise completion pulls back by composition).**

$$\forall mapState: S \to T, defect: T \to D, zero: D, x: S, \operatorname{ZeroAt}\left(defect \circ mapState, zero, x\right) \iff \operatorname{ZeroAt}\left(defect, zero, \operatorname{mapState}\left(x\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CompletionPoints/CompletionPointPullback.zero_at_pullback` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Map a source state into the target state space and evaluate the target defect there.

Zero defect for the composite at the source is definitionally equivalent to zero defect at the mapped target state.

**Theorem 1.2 (The pulled-back zero set is a preimage).**

$$\forall mapState: S \to T, defect: T \to D, zero: D, \operatorname{zeroSet}\left(defect \circ mapState, zero\right) = \operatorname{preimage}\left(mapState, \operatorname{zeroSet}\left(defect, zero\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CompletionPoints/CompletionPointPullback.zero_set_pullback` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Collect the source states where the composite defect vanishes.

This set is exactly the preimage under the state map of the target defect's zero set.

## References

- Truth anchor: `D5/S3/Observer/CompletionPoints/CompletionPointPullback.zero_at_pullback`
- Truth anchor: `D5/S3/Observer/CompletionPoints/CompletionPointPullback.zero_set_pullback`
