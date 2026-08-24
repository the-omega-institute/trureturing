# Indexed Target-Defect Monotonicity

## Abstract

Enlarging an indexed readout budget shrinks its target-defect relation.

**Theorem 1.1 (Larger observation budgets shrink target defects).**

$$\begin{gathered}\forall I, X, T: \operatorname{Type},\\{}O: I \to \operatorname{Type}, q: \forall i: I, X \to O(i),\\{}t: X \to T,\\{}J, K: \operatorname{Finset}\left(I\right), J \subseteq K \Rightarrow\\{}\operatorname{defectRelation}\left(\operatorname{jointReadout}\left(q, K\right), t\right) \subseteq \operatorname{defectRelation}\left(\operatorname{jointReadout}\left(q, J\right), t\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementFactorization/IndexedTargetDefectMonotonicity.larger_observation_budget_shrinks_target_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A single indexed observation family q constructs both public joint readouts by restricting q to J and K. The target-defect relation is the target-risk family's canonical predicate: equal readout coordinates together with unequal target values.

When J is contained in K, the existing indexed-readout theorem sends equality of the K-readouts to equality of the J-readouts. The target inequality is unchanged, yielding the displayed reverse inclusion of defect relations.

No sibling copy of the indexed readout, refinement relation, or defect predicate is introduced.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementFactorization/IndexedTargetDefectMonotonicity.larger_observation_budget_shrinks_target_defect`
- Dependency: [D5/S3/ConceptDynamics/RefinementFactorization/IndexedReadoutMonotonicity](IndexedReadoutMonotonicity.md)
- Dependency: [D5/S3/ConceptDynamics/TargetRisk/RefinementRiskCostTradeoff](../TargetRisk/RefinementRiskCostTradeoff.md)
