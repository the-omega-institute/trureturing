# Decorated Necklace Invariants

## Abstract

Cyclic rotation classes retain word length and decoration multiplicity without identifying reflections.

**Theorem 1.1 (Rotation classes retain length and multiplicity but distinguish reflection).**

$$\begin{aligned}\forall alpha: Type, u, v: \operatorname{List}\left(alpha\right),\\\operatorname{IsRotated}\left(u, v\right) \Leftrightarrow \exists n \in \mathbb{N}, v = \operatorname{rotate}\left(u, n\right),\\\operatorname{IsRotated}\left(u, v\right) \Rightarrow (\operatorname{length}\left(u\right) = \operatorname{length}\left(v\right) \land \operatorname{multiset}\left(u\right) = \operatorname{multiset}\left(v\right)),\\\forall W, w, n, \operatorname{systemNecklaces}\left(\operatorname{insert}\left(\operatorname{rotate}\left(w, n\right), W\right)\right) = \operatorname{systemNecklaces}\left(\operatorname{insert}\left(w, W\right)\right),\\\operatorname{necklace}\left(\operatorname{list}\left(1, 2, 3\right)\right) = \operatorname{necklace}\left(\operatorname{list}\left(2, 3, 1\right)\right) = \operatorname{necklace}\left(\operatorname{list}\left(3, 1, 2\right)\right),\\\operatorname{necklace}\left(\operatorname{list}\left(1, 2, 3\right)\right) \neq \operatorname{necklace}\left(\operatorname{list}\left(1, 3, 2\right)\right) \land \operatorname{multiset}\left(\operatorname{list}\left(1, 2, 3\right)\right) = \operatorname{multiset}\left(\operatorname{list}\left(1, 3, 2\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S0/Combinatorics/DecoratedNecklaceInvariant.decorated_necklace_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A necklace is Mathlib's quotient of lists by cyclic rotation. The underlying setoid relates two words exactly when the second is a rotation of the first; this includes the empty word and rotations by amounts larger than the word length.

A rotation preserves both list length and the multiset of decorations. Mapping a multiset of component words into rotation classes therefore defines the system invariant, and rotating any one component leaves that multiset of necklaces unchanged.

The words 1,2,3; 2,3,1; and 3,1,2 represent the same necklace. By contrast, 1,3,2 is not a rotation of 1,2,3 even though the two words have equal decoration multisets. Thus multiplicity is an invariant of a necklace, not a complete classification of necklaces.

## References

- Truth anchor: `D5/S0/Combinatorics/DecoratedNecklaceInvariant.decorated_necklace_invariant`
