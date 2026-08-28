# Recursive Intervention Composition

## Abstract

A recursively realized node value makes its additional intervention redundant.

**Theorem 1.1 (A realized intervention composes without changing the outcome).**

$$\forall n: \mathbb{N}, X, U: \operatorname{Type},\ model: \operatorname{StructuralModel}(n, X, U), intervention: \operatorname{Finset}(\operatorname{Fin}(n)), assigned: \operatorname{Fin}(n) \to X, u: U,\ baseResult, expandedResult: \operatorname{Fin}(n) \to X, w, y: \operatorname{Fin}(n),\ \operatorname{EvaluationWitness}(model, intervention, assigned, u, \operatorname{order}(model), \operatorname{initial}(model, u), baseResult) \land \operatorname{EvaluationWitness}(model, \operatorname{insert}(w, intervention), assigned, u, \operatorname{order}(model), \operatorname{initial}(model, u), expandedResult) \land baseResult(w) = assigned(w) \Rightarrow expandedResult(y) = baseResult(y).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/RecursiveInterventionComposition.recursive_intervention_composition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both worlds use the repository's parent-ordered structural model, the same external state, and the same assignment. The second world additionally intervenes at one node.

When the first evaluation already realizes the value assigned at that node, the inserted intervention performs the same update. Determinism of all later recursive updates then gives the same value at every queried outcome node.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Causal/RecursiveInterventionComposition.recursive_intervention_composition`
- Dependency: [D5/S3/ConceptDynamics/Causal/ParentOrderedStructuralEvaluationSemantics](ParentOrderedStructuralEvaluationSemantics.md)
