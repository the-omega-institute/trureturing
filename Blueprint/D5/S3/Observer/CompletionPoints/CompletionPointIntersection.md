# Completion Point Intersection

## Abstract

Paired zero-defect completion equals intersection of component completion conditions.

**Theorem 1.1 (Paired vanishing is componentwise vanishing).**

$$\forall first: X \to A, second: X \to B,\\{}a0: A, b0: B, s: X, \operatorname{ZeroAt}\left(x \mapsto \operatorname{pair}\left(\operatorname{first}\left(x\right), \operatorname{second}\left(x\right)\right), \operatorname{pair}\left(a0, b0\right), s\right) \iff (\operatorname{ZeroAt}\left(first, a0, s\right) \land \operatorname{ZeroAt}\left(second, b0, s\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CompletionPoints/CompletionPointIntersection.paired_zero_iff_component_zeros` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix two defect readouts, their designated zero values, and a state.

The paired defect equals the paired zero exactly when each component defect equals its corresponding zero.

**Theorem 1.2 (The paired zero set is the component intersection).**

$$\forall first: X \to A, second: X \to B,\\{}a0: A, b0: B, \operatorname{zeroSet}\left(x \mapsto \operatorname{pair}\left(\operatorname{first}\left(x\right), \operatorname{second}\left(x\right)\right), \operatorname{pair}\left(a0, b0\right)\right) = \operatorname{intersection}\left(\operatorname{zeroSet}\left(first, a0\right), \operatorname{zeroSet}\left(second, b0\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CompletionPoints/CompletionPointIntersection.paired_zero_set_eq_intersection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Collect all states where the paired defect vanishes.

By componentwise pair equality, this set is exactly the intersection of the first and second zero sets.

## References

- Truth anchor: `D5/S3/Observer/CompletionPoints/CompletionPointIntersection.paired_zero_iff_component_zeros`
- Truth anchor: `D5/S3/Observer/CompletionPoints/CompletionPointIntersection.paired_zero_set_eq_intersection`
