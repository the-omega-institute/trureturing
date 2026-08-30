# Minimum-Cost Target Cover

## Abstract

Target-sufficient finite intervention designs are exactly weighted covers of the target-disagreement pairs, including three boundary witnesses.

**Definition 1.1 (Target-disagreement pair universe).**

Lean statement: `D5/S3/ConceptDynamics/ExperimentOptimization/MinimumCostTargetCover.targetDisagreementPairs`

*Formalization.* `D5/S3/ConceptDynamics/ExperimentOptimization/MinimumCostTargetCover.targetDisagreementPairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The universe contains the unordered finite-model pairs on which the chosen target takes unequal values.

**Definition 1.2 (Pairs separated by an intervention).**

Lean statement: `D5/S3/ConceptDynamics/ExperimentOptimization/MinimumCostTargetCover.interventionSeparationSet`

*Formalization.* `D5/S3/ConceptDynamics/ExperimentOptimization/MinimumCostTargetCover.interventionSeparationSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An intervention contributes the target-disagreement pairs whose two models also have unequal responses under that intervention.

**Theorem 1.3 (Minimum-cost target sufficiency is weighted pair cover).**

$$\begin{aligned}\forall n: \mathbb{N}, A, Y: \operatorname{Type},\\R: A \to \operatorname{Type}, c: A \to \mathbb{R},\\q: \forall a: A, Fin(n) \to R(a), T: Fin(n) \to Y,\\J: Finset(A),\\\forall K: Finset(A), C(K) = \sum_{a \in K} c(a),\\(S(J) \land (\forall K: Finset(A), S(K) \Rightarrow C(J) \leq C(K))) \iff \\(Cover(J) \land (\forall K: Finset(A), Cover(K) \Rightarrow C(J) \leq C(K))).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ExperimentOptimization/MinimumCostTargetCover.minimum_cost_target_sufficient_design_iff_pair_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The imported target-sufficiency criterion identifies feasibility with coverage of exactly the target-disagreement universe.

The identical real-valued finite sum is minimized over the two extensionally equal feasible families, so no nonnegativity assumption on intervention costs is required.

**Theorem 1.4 (Zero costs make every sufficient design minimal).**

$$S(J) \Rightarrow\\{}S(J) \land (\forall K, \sum_{a \in J} 0 \leq \sum_{a \in K} 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ExperimentOptimization/MinimumCostTargetCover.zero_cost_target_sufficient_design_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When every selected summand is zero, any target-sufficient design has the same cost as every candidate.

**Theorem 1.5 (One identity intervention covers the two-state target).**

$$A = Unit, X = Fin(2), J = \{star\},\\{}q(star) = id, T = id \Rightarrow\\{}S(J) \land Cover(J).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ExperimentOptimization/MinimumCostTargetCover.singleton_intervention_cover_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On Fin 2, the sole identity readout is target-sufficient for the identity target and covers every target-disagreement pair.

**Theorem 1.6 (The empty horizon has an empty cover).**

$$n = 0, A = \emptyset, J = \emptyset,\\{}T = constant \Rightarrow\\{}S(J) \land Cover(J).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ExperimentOptimization/MinimumCostTargetCover.empty_target_cover_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At horizon zero, the empty intervention type and empty design are sufficient for the constant target and cover its empty pair universe.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ExperimentOptimization/MinimumCostTargetCover.empty_target_cover_witness`
- Truth anchor: `D5/S3/ConceptDynamics/ExperimentOptimization/MinimumCostTargetCover.interventionSeparationSet`
- Truth anchor: `D5/S3/ConceptDynamics/ExperimentOptimization/MinimumCostTargetCover.minimum_cost_target_sufficient_design_iff_pair_cover`
- Truth anchor: `D5/S3/ConceptDynamics/ExperimentOptimization/MinimumCostTargetCover.singleton_intervention_cover_witness`
- Truth anchor: `D5/S3/ConceptDynamics/ExperimentOptimization/MinimumCostTargetCover.targetDisagreementPairs`
- Truth anchor: `D5/S3/ConceptDynamics/ExperimentOptimization/MinimumCostTargetCover.zero_cost_target_sufficient_design_witness`
- Dependency: [D5/S3/ConceptDynamics/ExperimentDesign/TargetSufficiencyPairCover](../ExperimentDesign/TargetSufficiencyPairCover.md)
