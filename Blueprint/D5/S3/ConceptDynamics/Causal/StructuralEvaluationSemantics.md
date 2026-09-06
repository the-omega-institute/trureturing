# Structural Evaluation Semantics

## Abstract

A finite parent-ordered structural model has a unique post-intervention evaluation trace.

**Definition 1.1 (Intervention replaces exactly the selected structural equations).**

$$\forall n: \mathbb{N}, X, U: \operatorname{Type},\\{}model: \operatorname{StructuralModel}(n, X, U), intervention: \operatorname{Finset}(\operatorname{Fin}(n)),\\{}assigned: \operatorname{Fin}(n) \to X, v: \operatorname{Fin}(n), state: \operatorname{Fin}(n) \to X, u: U,\\{}\operatorname{intervenedEquation}(model, intervention, assigned, v, state, u) = \operatorname{if}(v \in intervention, \operatorname{assigned}(v), \operatorname{equation}(model, v, state, u)).$$

*Formalization.* `D5/S3/ConceptDynamics/Causal/StructuralEvaluationSemantics.intervenedEquation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given a finite-node structural model, an intervention set, and an assignment, the equation at node v returns the assigned value when v belongs to the intervention.

At every node outside the intervention it evaluates the model's original structural equation on the current state and external state. The displayed equality preserves both branches.

**Theorem 1.2 (Post-intervention structural evaluation is unique).**

$$\forall n: \mathbb{N}, X, U: \operatorname{Type},\ model: \operatorname{StructuralModel}(n, X, U), topological: \operatorname{TopologicalOrder}(model), intervention: \operatorname{Finset}(\operatorname{Fin}(n)), assigned: \operatorname{Fin}(n) \to X, u: U \Rightarrow \exists! result: \operatorname{Fin}(n) \to X, \operatorname{EvaluationWitness}(model, intervention, assigned, u, \operatorname{order}(model), \operatorname{initial}(model, u), result).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/StructuralEvaluationSemantics.structure_evaluation_semantics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The model carries finite nodes, parent sets, structural equations, and an external-state initialization. A supplied topological-order certificate places every parent before its child.

An intervention replaces the equations at its selected nodes by the assigned values. The displayed evaluation witness is the recursive state update along the supplied order, and the theorem proves a unique final assignment for every external state.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Causal/StructuralEvaluationSemantics.intervenedEquation`
- Truth anchor: `D5/S3/ConceptDynamics/Causal/StructuralEvaluationSemantics.structure_evaluation_semantics`
