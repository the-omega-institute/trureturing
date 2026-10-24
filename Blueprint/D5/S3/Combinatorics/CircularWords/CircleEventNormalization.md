# Free rotation normalizes circular events

## Abstract

Free rotation normalizes circular events

**Theorem 1.1 (Free rotation normalizes circular events).**

$$\forall alpha \in \mathrm{Type},\; \forall A \in \mathrm{Finset}\left(alpha\right),\; \forall P \in \mathrm{PredicatesOn}\left(\mathrm{Cycle}\left(alpha\right)\right),\; (\mathrm{Nonempty}\left(A\right)) \Rightarrow (\mathrm{card}\left(\mathrm{RootEvent}\left(A, P\right)\right) = \mathrm{card}\left(A\right) \cdot \mathrm{card}\left(\mathrm{CircleEvent}\left(A, P\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/CircleEventNormalization.event_order_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier has decidable equality. P is any predicate on Cycle(alpha). RootEvent(A,P) filters orders(A) by P of the actual rotation class; CircleEvent(A,P) filters circles(A) by P.

An actual order of n distinct labels has n distinct rotations. The image in Mathlib Cycle retains orientation and identifies precisely those rotations. Every circle fiber therefore has exactly n rooted original-label words.

For any predicate on these circles, the number of rooted orders in that event is n times the number of event circles. The paired Good criterion is transported to such a circle predicate before this formula is used. A linear block event alone is not assumed rotation invariant.

## References

- Truth anchor: `D5/S3/Combinatorics/CircularWords/CircleEventNormalization.event_order_card`
- Dependency: [D5/S3/Combinatorics/CircularWords/CircularOrderCount](CircularOrderCount.md)
