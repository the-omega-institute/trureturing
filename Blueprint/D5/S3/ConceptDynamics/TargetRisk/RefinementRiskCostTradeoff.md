# Refinement, Target Risk, and Cost

## Abstract

Refinement shrinks target risk while increasing attained-coordinate cost.

**Theorem 1.1 (Refinement reduces risk and raises coordinate cost).**

$$\forall X, C, D, T: \operatorname{Type}, q_{C}: X \to C, q_{D}: X \to D, \mathcal{T}: \operatorname{Set} {X \to T}, \operatorname{Refines}(q_{C}, q_{D}) \Rightarrow\ (\operatorname{targetRisk}(q_{D}, \mathcal{T}) \subseteq \operatorname{targetRisk}(q_{C}, \mathcal{T})) \land\ (\operatorname{refinementCost}(q_{C}) \le \operatorname{refinementCost}(q_{D})).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/TargetRisk/RefinementRiskCostTradeoff.refinement_reduces_target_risk_and_raises_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The defect relation consists of state pairs identified by a source readout but distinguished by a target. Target risk filters a supplied target family for targets with a nonempty defect relation.

A factor-map refinement preserves every equality seen by the finer readout, so each fine defect is also a coarse defect and fine target risk is contained in coarse target risk.

Cost is the extended cardinality of attained readout coordinates. The factor map sends the fine range onto the coarse range, so refinement cannot lower this cost. Coarser compression trades that cost benefit against a potentially larger future-risk set.

## References

- Truth anchor: `D5/S3/ConceptDynamics/TargetRisk/RefinementRiskCostTradeoff.refinement_reduces_target_risk_and_raises_cost`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
