# Refinement-Monotone Answer Domain

## Abstract

Canonical safe answers and their admitted answer domain grow monotonically under concept refinement.

**Theorem 1.1 (Refinement preserves the canonical answer value).**

$$\forall X \in Type, C \in Type, D \in Type, Y \in Type, A \in X \to Prop, qC \in X \to C, qD \in X \to D, T \in X \to Y, x \in X, y \in Y,\; \left(\operatorname{Refines}\left(q_{C}, q_{D}\right) \land \left(A\left(x\right) \land \operatorname{canonicalSafeAnswer}\left(A, q_{C}, T, \left(q_{C}\right)\left(x\right)\right) = \operatorname{some}\left(y\right)\right)\right) \Rightarrow \operatorname{canonicalSafeAnswer}\left(A, q_{D}, T, \left(q_{D}\right)\left(x\right)\right) = \operatorname{some}\left(y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Answering/RefinementMonotoneAnswerDomain.refinement_monotone_answer_domain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose a coarse concept canonically answers y at an admitted state x. A refinement splits coarse fibers without merging distinct ones, so every state in the refined fiber of x still has target y.

The coarse canonical answer supplies a zero-error answerer on refined fibers by composition with the factor map. Since x inhabits the relevant refined fiber, safe-answer coverage maximality forces the refined canonical answer to return the same value y.

**Lemma 1.2 (The admitted answer domain is monotone under refinement).**

$$\forall X \in Type, C \in Type, D \in Type, Y \in Type, A \in X \to Prop, qC \in X \to C, qD \in X \to D, T \in X \to Y,\; \operatorname{Refines}\left(q_{C}, q_{D}\right) \Rightarrow \operatorname{answerDomain}\left(A, q_{C}, T\right) \subseteq \operatorname{answerDomain}\left(A, q_{D}, T\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Answering/RefinementMonotoneAnswerDomain.answer_domain_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The answer domain contains exactly the admitted states where the canonical safe answerer returns some target value. Extracting that value and applying answer preservation shows that every state answered by a coarse concept is also answered by any refinement.

The Boolean smoke instance shows that the containment can be strict: a constant concept cannot safely distinguish false from true, while the identity refinement answers both admitted states.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Answering/RefinementMonotoneAnswerDomain.answer_domain_monotone`
- Truth anchor: `D5/S3/ConceptDynamics/Answering/RefinementMonotoneAnswerDomain.refinement_monotone_answer_domain`
- Dependency: [D5/S3/ConceptDynamics/Answering/SafeAnswerCoverageMaximality](SafeAnswerCoverageMaximality.md)
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
