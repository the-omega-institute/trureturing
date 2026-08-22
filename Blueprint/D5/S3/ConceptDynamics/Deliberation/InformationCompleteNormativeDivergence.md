# Information-Complete Normative Divergence

## Abstract

With distinct normative values, complete information permits disagreement; incomplete information permits consensus blind to a Boolean target.

**Theorem 1.1 (Complete information permits normative divergence).**

$$\begin{gathered}(\forall X, I, U: \operatorname{Type},\\{}\forall concept: \operatorname{Concept}\left(X, I\right),\\{}\forall leftValue, rightValue: U,\\{}(\operatorname{Nonempty}\left(X\right) \land leftValue \neq rightValue \land \operatorname{Injective}\left(concept\right)) \Rightarrow\\{}\exists leftNorm, rightNorm: \operatorname{Concept}\left(X, U\right),\\{}\exists witness: X, leftNorm(witness) \neq rightNorm(witness)) \land\\{}(\forall X, I: \operatorname{Type},\\{}\forall concept: \operatorname{Concept}\left(X, I\right),\\{}\neg \operatorname{Injective}\left(concept\right) \Rightarrow\\{}\exists leftNorm, rightNorm, target: \operatorname{Concept}\left(X, Bool\right),\\{}\operatorname{NormativeConsensus}\left(leftNorm, rightNorm\right) \land\\{}\neg (\exists answer: I \to Bool, target = answer \circ concept)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Deliberation/InformationCompleteNormativeDivergence.complete_information_permits_normative_divergence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any nonempty state type and any two distinct normative values, an injective concept admits two normative functions that disagree at a state. The constant functions at the chosen values provide the disagreement, so informational completeness does not impose a unique norm.

For every noninjective concept, two equal Boolean normative functions witness consensus while a Boolean target remains impossible to recover from the concept. Consensus here is equality of the two normative functions, not a claim that all possible norms agree.

A collision in the concept fiber supplies the separating target: it distinguishes states that the concept identifies, and therefore cannot factor through any Boolean answer on the concept's codomain. Agreement can thus coexist with blindness to a relevant target.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Deliberation/InformationCompleteNormativeDivergence.complete_information_permits_normative_divergence`
- Dependency: [D5/S3/ConceptDynamics/Contracts/FutureObligationIncompleteness](../Contracts/FutureObligationIncompleteness.md)
