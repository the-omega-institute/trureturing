# Nonnegative Value of Free Information

## Abstract

A free ignorable observation cannot lower optimal expected value.

**Theorem 1.1 (Free ignorable information has nonnegative value).**

$$\begin{aligned}\forall X, E, U: \operatorname{Type},\\{}\forall \mathbb{E}: \operatorname{Concept}\left(X \to \mathbb{R}, \mathbb{R}\right),\\{}\forall observe: \operatorname{Concept}\left(X, E\right), worldAfterObservation: E \to X \to X,\\{}\forall V: \operatorname{Concept}\left(X, U \to \mathbb{R}\right), informationCost: \mathbb{R},\\{}\forall A0: \operatorname{Set}\left(U\right), A1: E \to \operatorname{Set}\left(U\right),\\{}\forall P: \operatorname{Set}\left(E \to U\right), W_{0}, W_{E}: \mathbb{R},\\{}\forall informationFree: informationCost = 0,\\{}\forall observationDoesNotChangeWorld: \forall e: E, x: X, worldAfterObservation(e, x) = x,\\{}\forall canIgnoreInformation: \forall u: U, u \in A0 \Rightarrow (e: E) \mapsto u \in P,\\{}\forall actionSetNotReduced: \forall e: E, A0 \subseteq A1(e),\\{}\forall uninformedOptimal: \operatorname{IsGreatest}\left(\operatorname{image}\left(\operatorname{uninformedExpectedValue}\left(\mathbb{E}, V\right), A0\right), W_{0}\right),\\{}\forall informedOptimal: \operatorname{IsGreatest}\left(\operatorname{image}\left(\operatorname{informedExpectedValue}\left(\mathbb{E}, observe, worldAfterObservation, V, informationCost\right), \operatorname{admissiblePolicies}\left(P, A1\right)\right), W_{E}\right),\\{}W_{0} \leq W_{E}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DecisionValue/FreeInformationValue.free_ignorable_information_value_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The uninformed value is the greatest expected utility obtained by choosing one available action. The informed value is the greatest net expected utility of an admissible observation-dependent policy.

The four safeguards are public. Information has zero cost, observation leaves the state unchanged, every constant policy is a permitted way to ignore the observation, and every previously available action remains available after each observation.

Choose an action attaining the uninformed optimum. Its constant policy is both permitted and pointwise available by the last two safeguards. The first two safeguards make its informed net value equal to the uninformed optimum, so informed optimality gives the inequality.

The expectation functional, observation, world transition, utility, costs, action sets, and policy set are independent source inputs. Repository and pinned-library searches found no exact theorem combining them.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DecisionValue/FreeInformationValue.free_ignorable_information_value_nonnegative`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../ConceptFiberDecomposition.md)
