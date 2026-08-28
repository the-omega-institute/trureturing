# Static Exact Experiment Design

## Abstract

Two complementary change experiments are jointly exact, and every exact static selection contains both.

**Theorem 1.1 (Both complementary experiments are necessary and sufficient).**

$$\begin{aligned}\forall m: \operatorname{Fin}(3), E_{X}(m):= \operatorname{decide}(m = 1),\\\forall m: \operatorname{Fin}(3), E_{Y}(m):= \operatorname{decide}(m = 2),\\\forall e: Bool, m: \operatorname{Fin}(3), q(e, m):= \operatorname{if}(e, E_{Y}(m), E_{X}(m)),\\(\forall e: Bool, \neg\operatorname{Injective}(\operatorname{readoutAt}(q, e))) \land \operatorname{Injective}(\operatorname{jointReadout}(q)) \land (\forall J: \operatorname{Finset}(Bool), \operatorname{Injective}(\operatorname{jointReadout}(\operatorname{restrict}(q, J))) \Rightarrow J = \{false, true\}).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ExperimentDesign/StaticExactExperimentDesign.static_exact_design` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state carrier has three model labels. The false experiment role detects only label one, while the true role detects only label two.

Each response alone merges two labels. Their canonical joint readout is injective, and an injective static selection of the two roles must be the full Boolean selection.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ExperimentDesign/StaticExactExperimentDesign.static_exact_design`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../Faithfulness/JointFaithfulnessLeibnizCriterion.md)
