# Minimum Audit Set Cover

## Abstract

Minimum target-complete audit suites are minimum defect set covers.

**Theorem 1.1 (Minimum complete audit suites are minimum defect covers).**

$$\forall X \in Type, C \in Type, T \in Type, I \in Type, O \in I \to Type, c \in X \to C, t \in X \to T, q \in \forall i: I, X \to O\left(i\right), J \in \operatorname{Finset}\left(I\right),\; \operatorname{let} Complete(K: \operatorname{Finset}\left(I\right)) := \forall x \in X, y \in X,\; (c\left(x\right), \operatorname{jointReadout}\left(\operatorname{restrict}\left(q, K\right), x\right)) = (c\left(y\right), \operatorname{jointReadout}\left(\operatorname{restrict}\left(q, K\right), y\right)) \Rightarrow t\left(x\right) = t\left(y\right); \operatorname{let} Covers(K: \operatorname{Finset}\left(I\right)) := \operatorname{Union}\left(i \in K, \left\{q\left(i\right)\left(\operatorname{fst}\left(p\right)\right) \ne q\left(i\right)\left(\operatorname{snd}\left(p\right)\right) \mid p \in \operatorname{defectRelation}\left(c, t\right)\right\}\right) = \operatorname{defectRelation}\left(c, t\right); \left(\operatorname{Complete}\left(J\right) \land \left(\forall L \in \operatorname{Finset}\left(I\right),\; \operatorname{Complete}\left(L\right) \Rightarrow \operatorname{card}\left(J\right) \le \operatorname{card}\left(L\right)\right)\right) \Leftrightarrow \left(\operatorname{Covers}\left(J\right) \land \left(\forall L \in \operatorname{Finset}\left(I\right),\; \operatorname{Covers}\left(L\right) \Rightarrow \operatorname{card}\left(J\right) \le \operatorname{card}\left(L\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Audits/MinimumAuditSetCover.minimum_audit_set_is_set_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The current and target concepts construct the canonical defect relation. Each test covers exactly the defects on which its response differs.

Completeness is stated on the canonical joint readout of a selected finite suite. The theorem transports both feasibility and cardinality comparison against every candidate suite, so no optimizer is assumed to exist.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Audits/MinimumAuditSetCover.minimum_audit_set_is_set_cover`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../Faithfulness/JointFaithfulnessLeibnizCriterion.md)
- Dependency: [D5/S3/ConceptDynamics/TargetRisk/RefinementRiskCostTradeoff](../TargetRisk/RefinementRiskCostTradeoff.md)
