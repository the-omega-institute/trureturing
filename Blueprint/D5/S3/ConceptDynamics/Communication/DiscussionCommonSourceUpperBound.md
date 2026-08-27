# Discussion Common-Source Upper Bound

## Abstract

The joint discussion readout and its join with a bounded initial concept remain below their common source.

**Theorem 1.1 (Discussion preserves a common-source upper bound).**

$$\begin{aligned}\forall I, X, B: \operatorname{Type}, M: I \to \operatorname{Type},\\m: \forall i: I, X \to M_{i}, s: X \to B,\\(\forall i: I, \operatorname{Refines}\left(m\left(i\right), s\right)) \Rightarrow \\\operatorname{Refines}\left(\operatorname{jointReadout}\left(m\right), s\right) \land \\(\forall C0: \operatorname{Type}, c0: X \to C0, \operatorname{Refines}\left(c0, s\right) \Rightarrow \\\operatorname{Refines}\left(\operatorname{conceptJoin}\left(c0, \operatorname{jointReadout}\left(m\right)\right), s\right)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Communication/DiscussionCommonSourceUpperBound.discussion_common_source_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first clause applies the canonical indexed common-source theorem to the complete dependent message readout.

For the second clause, the concept-join universal property combines the initial-concept bound with the derived message bound.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Communication/DiscussionCommonSourceUpperBound.discussion_common_source_upper_bound`
- Dependency: [D5/S3/ConceptDynamics/Communication/IndexedCommonSourceUpperBound](IndexedCommonSourceUpperBound.md)
