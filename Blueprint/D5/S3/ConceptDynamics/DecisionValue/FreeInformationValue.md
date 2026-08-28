# Nonnegative Value of Free Information

## Abstract

A free ignorable observation cannot lower optimal expected value.

**Theorem 1.1 (Free ignorable information has nonnegative value).**

$$\begin{aligned}\forall State, Evidence, Action: \operatorname{Type},\\{}\forall expectation: \operatorname{Concept}\left(State \to \mathbb{R}, \mathbb{R}\right),\\{}\forall observe: \operatorname{Concept}\left(State, Evidence\right), worldAfterObservation: Evidence \to State \to State,\\{}\forall utility: \operatorname{Concept}\left(State, Action \to \mathbb{R}\right), informationCost: \mathbb{R},\\{}\forall actionsBeforeObservation: \operatorname{Set}\left(Action\right), actionsAfterObservation: Evidence \to \operatorname{Set}\left(Action\right),\\{}\forall candidatePolicies: \operatorname{Set}\left(Evidence \to Action\right), uninformedValue, informedValue: \mathbb{R},\\{}\forall informationFree: informationCost = 0,\\{}\forall observationDoesNotChangeWorld: \forall evidence: Evidence, state: State, worldAfterObservation(evidence, state) = state,\\{}\forall canIgnoreInformation: \forall action: Action, action \in actionsBeforeObservation \Rightarrow (evidence: Evidence) \mapsto action \in candidatePolicies,\\{}\forall actionSetNotReduced: \forall evidence: Evidence, actionsBeforeObservation \subseteq actionsAfterObservation(evidence),\\{}\forall uninformedOptimal: \operatorname{IsGreatest}\left(\operatorname{image}\left(\operatorname{uninformedExpectedValue}\left(expectation, utility\right), actionsBeforeObservation\right), uninformedValue\right),\\{}\forall informedOptimal: \operatorname{IsGreatest}\left(\operatorname{image}\left(\operatorname{informedExpectedValue}\left(expectation, observe, worldAfterObservation, utility, informationCost\right), \operatorname{admissiblePolicies}\left(candidatePolicies, actionsAfterObservation\right)\right), informedValue\right),\\{}uninformedValue \leq informedValue.\end{aligned}$$

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
