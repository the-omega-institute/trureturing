# Observer-Relative Action Rule Decidability

## Abstract

Actor-relative readability is preserved exactly by compatible transitions.

**Theorem 1.1 (Readability of the three action-rule forms).**

$$\begin{gathered}\forall X, U, I: \operatorname{Type},\\{}B: I \to \operatorname{Type}, q: \forall k: I, X \to B\left(k\right),\\{}F: X \to \left(U \to \left(I \to \left(I \to X\right)\right)\right), i: I,\\{}Q: X \times U \times I \to B\left(i\right) \times U \times I := \Lambda z: X \times U \times I, \operatorname{triple}\left(q\left(i\right)\left(\operatorname{state}\left(z\right)\right), \operatorname{action}\left(z\right), \operatorname{recipient}\left(z\right)\right),\\{}M: X \times U \times I \to X := \Lambda z: X \times U \times I, F\left(\operatorname{state}\left(z\right), \operatorname{action}\left(z\right), \operatorname{recipient}\left(z\right), i\right),\\{}A: X \times U \times I \to X := \Lambda z: X \times U \times I, F\left(\operatorname{state}\left(z\right), \operatorname{action}\left(z\right), i, \operatorname{recipient}\left(z\right)\right),\\{}[(\operatorname{FactorsThrough}\left(\operatorname{compose}\left(q\left(i\right), M\right), Q\right) \Leftrightarrow \left(\forall W \in X \to Prop,\; \operatorname{FactorsThrough}\left(W, q\left(i\right)\right) \Rightarrow \operatorname{FactorsThrough}\left(\Lambda z: X \times U \times I, \neg W\left(M\left(z\right)\right), Q\right)\right)) \land\\{}(\forall W \in X \to Prop, C \in X \times U \times I \to Prop,\; \left(\operatorname{FactorsThrough}\left(W, q\left(i\right)\right) \land \left(\operatorname{FactorsThrough}\left(C, Q\right) \land \operatorname{FactorsThrough}\left(\operatorname{compose}\left(q\left(i\right), M\right), Q\right)\right)\right) \Rightarrow \operatorname{FactorsThrough}\left(\Lambda z: X \times U \times I, W\left(M\left(z\right)\right) \land C\left(z\right), Q\right)) \land\\{}(\forall V \in \forall j: I, X \to Prop,\; \operatorname{FactorsThrough}\left(\Lambda z: X \times U \times I, \neg V\left(\operatorname{recipient}\left(z\right), A\left(z\right)\right), Q\right) \Leftrightarrow \operatorname{FactorsThrough}\left(\Lambda z: X \times U \times I, V\left(\operatorname{recipient}\left(z\right), A\left(z\right)\right), Q\right))].\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/NormativeStructure/ObserverActionRuleDecidability.observer_action_rule_decidability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actor readout, transition, mirrored transition, actual transition, and actor-visible action input are constructed explicitly on the source carrier.

Transition compatibility is equivalent to readability of every negative mirrored wish. This includes the source converse: an incompatible transition is separated by a readable wish.

Under the same compatibility, a readable wish conjoined with a readable capability remains readable. For the actual transition evaluated by another recipient's wish, readability of the negated rule is exactly readability of the pulled-back wish itself.

## References

- Truth anchor: `D5/S3/ConceptDynamics/NormativeStructure/ObserverActionRuleDecidability.observer_action_rule_decidability`
