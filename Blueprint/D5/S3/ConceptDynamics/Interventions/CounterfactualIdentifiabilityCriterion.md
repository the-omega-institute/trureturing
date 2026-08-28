# Counterfactual Identifiability Criterion

## Abstract

Counterfactual recovery from all single-world marginals is exactly constancy on coupling fibers, and complete Boolean counterfactuals fail this criterion.

**Theorem 1.1 (Single-world identifiability is constancy on coupling fibers).**

$$\begin{gathered}\forall Value: \operatorname{Type}, [\operatorname{Nonempty} Value],\\{}Q: BooleanCoupling \to Value,\\{}\left(\exists f \in (Bool \to BooleanMarginal) \to Value,\; Q = f \circ allSingleWorldMarginals\right) \Leftrightarrow \left(\forall mu \in Bool \to BooleanMarginal, M \in BooleanCoupling, N \in BooleanCoupling,\; \left(M \in couplingFiber\left(allSingleWorldMarginals, mu\right) \land N \in couplingFiber\left(allSingleWorldMarginals, mu\right)\right) \Rightarrow Q\left(M\right) = Q\left(N\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interventions/CounterfactualIdentifiabilityCriterion.boolean_counterfactual_identifiable_iff_constant_on_coupling_fibers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The observable record of a deterministic Boolean joint model is the family of outcome-count marginals indexed by intervention. A target Q is recoverable from that record exactly when any two models in the same explicitly represented coupling fiber have the same Q-value.

This specializes the general factorization criterion: a target factors through an observable map exactly when it is constant on every fiber. Nonemptiness of the target type permits the factor map to be extended to observable records outside the map's image.

**Lemma 1.2 (The complete counterfactual varies within one coupling fiber).**

$$\exists mu \in Bool \to BooleanMarginal, M \in BooleanCoupling, N \in BooleanCoupling,\; M \in couplingFiber\left(allSingleWorldMarginals, mu\right) \land \left(N \in couplingFiber\left(allSingleWorldMarginals, mu\right) \land CF\left(M\right) \ne CF\left(N\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interventions/CounterfactualIdentifiabilityCriterion.boolean_counterfactual_varies_on_coupling_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two deterministic Boolean joint models have the same marginal outcome counts under every intervention, so they occupy a single fiber of the all-single-world-marginals map.

Their complete unit-level counterfactual tables nevertheless differ. The observable fiber therefore contains a concrete variation of the counterfactual target.

**Lemma 1.3 (The complete Boolean counterfactual is not identifiable).**

$$\neg \left(\exists f \in (Bool \to BooleanMarginal) \to Bool \to \left(Bool \to \left(Bool \to Bool\right)\right),\; CF = f \circ allSingleWorldMarginals\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interventions/CounterfactualIdentifiabilityCriterion.boolean_counterfactual_not_identifiable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the complete unit-level counterfactual table could be recovered from all single-world intervention marginals, the fiber criterion would make it constant on every coupling fiber.

The two-model fiber witness has identical observable marginals but different counterfactual tables, contradicting that required constancy and ruling out every such recovery map.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Interventions/CounterfactualIdentifiabilityCriterion.boolean_counterfactual_identifiable_iff_constant_on_coupling_fibers`
- Truth anchor: `D5/S3/ConceptDynamics/Interventions/CounterfactualIdentifiabilityCriterion.boolean_counterfactual_not_identifiable`
- Truth anchor: `D5/S3/ConceptDynamics/Interventions/CounterfactualIdentifiabilityCriterion.boolean_counterfactual_varies_on_coupling_fiber`
- Dependency: [D5/S3/ConceptDynamics/Interventions/InterventionCounterfactualSeparation](InterventionCounterfactualSeparation.md)
