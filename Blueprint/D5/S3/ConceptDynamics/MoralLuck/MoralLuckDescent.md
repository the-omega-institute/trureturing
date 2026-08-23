# Control Descent and Fiber Defects

## Abstract

Control descent is equivalent to the absence of a fiber defect.

**Theorem 1.1 (Control descent iff no moral-luck witness).**

$$\forall X, B, L: \operatorname{Type}, [\operatorname{Fintype}(X)], [\operatorname{Fintype}(B)], [\operatorname{Fintype}(L)], [\operatorname{Nonempty}(X)],\ C: X \to B, J: X \to L,\ \exists d: B \to L, J = d \circ C \iff \neg \exists x, y,\ C(x) = C(y) \land J(x) \neq J(y).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/MoralLuck/MoralLuckDescent.moral_luck_descent_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite inhabited state type X, a control readout C, and an evaluation J, the control principle is the existence of a factor map from control values to evaluation values.

A witness is a pair of states with equal control values and unequal evaluations. The repository's answerability criterion supplies the factorization iff fiber-constancy step, which is exactly the negation of the witness predicate.

This formalizes the finite combinatorial kernel of theorem/40.1. The normative choice between control-based and outcome-based evaluation is intentionally not represented.

## References

- Truth anchor: `D5/S3/ConceptDynamics/MoralLuck/MoralLuckDescent.moral_luck_descent_iff`
- Dependency: [D5/S0/Rewriting/Quotients/AnswerabilityCriterion](../../../S0/Rewriting/Quotients/AnswerabilityCriterion.md)
