# Minimal Predictive Completion Quotient

## Abstract

The maximal forward congruence inside the readout kernel yields the coarsest quotient that preserves both the current readout and the state update.

**Lemma 1.1 (The readout relation is an equivalence).**

$$\begin{gathered}\forall X, O: \operatorname{Type},\\{}q: X \to O,\\{}\operatorname{Equivalence}\left(\operatorname{readoutRelation}\left(q\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/MinimalPredictiveCompletionQuotient.readout_relation_equivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The readout relation identifies two states exactly when their current observations agree. Reflexivity, symmetry, and transitivity are therefore inherited directly from equality in the observation space.

No state is chosen in this argument, so the equivalence law remains valid when the state type is empty. This supplies the setoid structure needed to form the predictive quotient.

**Theorem 1.2 (The predictive quotient is the coarsest completion).**

$$\begin{gathered}\forall X, O: \operatorname{Type},\\{}F: X \to X, q: X \to O,\\{}\exists qbar: \operatorname{PredictiveQuotient}\left(F, q\right) \to O, Fbar: \operatorname{PredictiveQuotient}\left(F, q\right) \to \operatorname{PredictiveQuotient}\left(F, q\right),\\{}q = qbar \circ \operatorname{predictiveProjection}\left(F, q\right) \land\\{}\operatorname{predictiveProjection}\left(F, q\right) \circ F = Fbar \circ \operatorname{predictiveProjection}\left(F, q\right) \land\\{}(\forall S: \operatorname{Setoid}\left(X\right),\\{}\operatorname{TauCongruence}\left(F, \operatorname{setoidRelation}\left(S\right)\right) \Rightarrow\\{}\operatorname{setoidRelation}\left(S\right) \subseteq \operatorname{readoutRelation}\left(q\right) \Rightarrow\\{}\operatorname{Refines}\left(\operatorname{predictiveProjection}\left(F, q\right), \operatorname{QuotientMk}\left(S\right)\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/MinimalPredictiveCompletionQuotient.minimal_predictive_completion_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The predictive setoid uses the largest forward congruence contained in the kernel of the current readout. Its quotient projection therefore forgets only distinctions that are observationally invisible now and remain compatible with one update step.

Containment in the readout kernel makes the readout descend to the quotient, while forward congruence makes the state update descend. The two displayed factorization equations say respectively that the quotient preserves the present observation and carries the dynamics.

Every other setoid that is a forward congruence and lies inside the readout kernel is contained in this maximal congruence. Hence the predictive projection factors through that setoid's quotient projection. With Refines(coarse, fine) meaning that the coarse readout factors through the fine one, this is precisely the stated coarseness direction.

The construction assumes neither finiteness nor inhabitedness. Empty state spaces, singleton observation spaces, identity updates, and constant readouts are therefore covered without separate cases.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/MinimalPredictiveCompletionQuotient.minimal_predictive_completion_quotient`
- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/MinimalPredictiveCompletionQuotient.readout_relation_equivalence`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
- Dependency: [D5/S3/Observer/Separation/CongruenceKernel](../../Observer/Separation/CongruenceKernel.md)
