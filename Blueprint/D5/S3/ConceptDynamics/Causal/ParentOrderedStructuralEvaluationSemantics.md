# Parent-Ordered Structural Evaluation Semantics

## Abstract

A finite parent-ordered structural model has a unique post-intervention evaluation trace.

**Theorem 1.1 (Parent-ordered structural evaluation is unique).**

$$\forall n: \mathbb{N}, X, U: \operatorname{Type},\ model: \operatorname{StructuralModel}(n, X, U), topological: \operatorname{TopologicalOrder}(model), intervention: \operatorname{Finset}(\operatorname{Fin}(n)), assigned: \operatorname{Fin}(n) \to X, u: U \Rightarrow \exists! result: \operatorname{Fin}(n) \to X, \operatorname{EvaluationWitness}(model, intervention, assigned, u, \operatorname{order}(model), \operatorname{initial}(model, u), result).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/ParentOrderedStructuralEvaluationSemantics.parent_ordered_structure_evaluation_semantics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The model carries finite nodes, parent sets, structural equations whose inputs are parent coordinates, and an external-state initialization. A supplied topological-order certificate places each parent before its child.

An intervention replaces the equations at its selected nodes by the assigned values. The displayed evaluation witness is the recursive state update along the supplied order, and the theorem proves a unique final assignment for every external state.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Causal/ParentOrderedStructuralEvaluationSemantics.parent_ordered_structure_evaluation_semantics`
