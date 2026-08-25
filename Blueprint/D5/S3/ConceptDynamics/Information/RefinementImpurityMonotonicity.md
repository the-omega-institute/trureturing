# Refinement Lowers Conditional Logical Impurity

## Abstract

Factor-map refinement cannot increase conditional logical impurity.

**Theorem 1.1 (Refinement cannot increase impurity).**

$$\begin{gathered}\forall X, C, D, A: \operatorname{Type},\\{}mu: \operatorname{PMF}(X),\\{}coarse: X \to C, refined: X \to D,\\{}target: X \to A,\\{}\operatorname{Refines}(coarse, refined) \Rightarrow\\{}\operatorname{conditionalLogicalImpurity}(mu, refined, target) \leq \operatorname{conditionalLogicalImpurity}(mu, coarse, target).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Information/RefinementImpurityMonotonicity.refinement_impurity_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A coarse concept fiber is the union of the refined fibers selected by the refinement factor map.

The countable Cauchy inequality bounds each coarse target-collision term by the corresponding refined terms. The complementary pair-disagreement normalization then reverses this comparison for conditional logical impurity.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Information/RefinementImpurityMonotonicity.refinement_impurity_monotone`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
- Dependency: [D5/S3/ConceptDynamics/Information/ConditionalLogicalImpurity](ConditionalLogicalImpurity.md)
