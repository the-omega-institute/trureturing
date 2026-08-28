# Intervention Effectiveness

## Abstract

A structural intervention fixes every selected coordinate at its assigned value.

**Theorem 1.1 (Intervened coordinates equal their assigned values).**

$$\forall n: \mathbb{N}, X, U: \operatorname{Type},\ model: \operatorname{StructuralModel}(n, X, U), intervention: \operatorname{Finset}(\operatorname{Fin}(n)), assigned: \operatorname{Fin}(n) \to X, u: U, result: \operatorname{Fin}(n) \to X, v: \operatorname{Fin}(n),\ \operatorname{EvaluationWitness}(model, intervention, assigned, u, \operatorname{order}(model), \operatorname{initial}(model, u), result) \land v \in intervention \Rightarrow result(v) = assigned(v).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/InterventionEffectiveness.intervention_effectiveness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The model uses the repository's parent-ordered structural semantics. An intervention replaces each selected structural equation by its assigned value, and the evaluation witness records the resulting updates through the complete node order.

The selected node is updated exactly once because the model order is complete and duplicate-free. All later updates occur at distinct nodes, so the selected coordinate retains its assigned value in the final result.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Causal/InterventionEffectiveness.intervention_effectiveness`
- Dependency: [D5/S3/ConceptDynamics/Causal/ParentOrderedStructuralEvaluationSemantics](ParentOrderedStructuralEvaluationSemantics.md)
