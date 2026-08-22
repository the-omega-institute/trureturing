# Anchor Full Identification

## Abstract

Full anchored identification is equivalent to reachability and injective behavior.

**Theorem 1.1 (Full identification from an anchor).**

$$\forall X, Y: \operatorname{Type}, a: X, R: X \to \operatorname{Set}\left(X\right), beta: X \to Y,\ ((R(a) = X \land \operatorname{HasLeftInverse}\left(beta\right)) \iff (R(a) = X \land \operatorname{Injective}\left(beta\right))) \land\ (R(a) \neq X \Rightarrow \exists x: X, \neg x \in R(a)) \land\ (R(a) = X \Rightarrow \neg \operatorname{Injective}\left(beta\right) \Rightarrow \exists x, y: X, x \in R(a) \land y \in R(a) \land beta(x) = beta(y) \land x \neq y).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Identifiability/AnchorFullIdentification.anchor_full_identification_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The anchored reachability set is the full state carrier exactly in the first conjunct. Full recovery from the behavior readout is expressed by the library predicate `HasLeftInverse`; its witness is a decoder that recovers every state from its complete behavior.

Pinned Mathlib identifies existence of such a decoder with injectivity of the behavior map. The theorem applies that equivalence directly and keeps the independent reachability condition unchanged.

If anchored reachability is not the full carrier, the second conjunct exhibits a state outside it. If reachability is full but behavior is not injective, the final conjunct exhibits two reachable, distinct states with the same complete behavior.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Identifiability/AnchorFullIdentification.anchor_full_identification_iff`
