# Conservative Extension Answerability

## Abstract

Answerability of old questions is reflected and preserved by surjective pullback.

**Theorem 1.1 (Surjective pullback preserves and reflects answerability).**

$$\forall X, Y, Cval, Tval: \operatorname{Type},\ p: Y \to X, C: \operatorname{Concept}(X, Cval), T: \operatorname{Concept}(X, Tval),\ \operatorname{Surjective}\left(p\right) \Rightarrow (\operatorname{Refines}\left(T, C\right) \iff \operatorname{Refines}\left(T \circ p, C \circ p\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Transport/ConservativeExtensionAnswerability.answerability_transports_along_surjection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a new state space project surjectively onto an old state space. An old target readout factors through an old concept exactly when their pullbacks along the projection have the same factorization.

The forward direction reuses the old factor map after pullback. For the reverse direction, surjectivity ensures that equality on all new states reflects equality on every old state. Thus the extension neither loses an old answer nor creates a spurious one.

**Lemma 1.2 (A non-surjective pullback can hide unanswerability).**

$$\neg \operatorname{Surjective}\left(nonSurjectiveProjection\right) \land\ \operatorname{Refines}\left(id \circ nonSurjectiveProjection, constantOldConcept \circ nonSurjectiveProjection\right) \land\ \neg \operatorname{Refines}\left(id, constantOldConcept\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Transport/ConservativeExtensionAnswerability.nonsurjective_pullback_can_hide_unanswerability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The one-state projection reaches only false in the old Boolean state space, while the old concept identifies both Boolean states. On the one visible state, the pulled-back identity target is constant and therefore factors through the pulled-back old concept.

On the full old state space, the Boolean identity cannot factor through that constant concept: a single factor value would have to equal both false and true. This counterexample shows that surjectivity is essential for reflecting old-state answerability.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Transport/ConservativeExtensionAnswerability.answerability_transports_along_surjection`
- Truth anchor: `D5/S3/ConceptDynamics/Transport/ConservativeExtensionAnswerability.nonsurjective_pullback_can_hide_unanswerability`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
