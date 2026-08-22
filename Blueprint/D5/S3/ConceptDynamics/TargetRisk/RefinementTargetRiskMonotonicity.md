# Refinement Monotonicity of Target Risk

## Abstract

Factor-map refinement monotonically shrinks target risk.

**Theorem 1.1 (Refinement monotonically shrinks target risk).**

$$\forall X, C, D, T: \operatorname{Type},\\{}q_{C}: X \to C, q_{D}: X \to D,\\{}\mathcal{T}: \operatorname{Set} {X \to T},\\{}\operatorname{Refines}(q_{C}, q_{D}) \Rightarrow \operatorname{targetRisk}(q_{D}, \mathcal{T}) \subseteq \operatorname{targetRisk}(q_{C}, \mathcal{T}).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/TargetRisk/RefinementTargetRiskMonotonicity.refinement_monotone_target_risk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public statement uses the family's frozen factor-map refinement, defect relation, and target-risk definitions. A finer readout cannot create a risky target absent from the coarser readout.

The proof directly applies the risk-inclusion projection of the frozen refinement theorem. The qualitative source remark about typical cost is deliberately outside this boxed theorem.

## References

- Truth anchor: `D5/S3/ConceptDynamics/TargetRisk/RefinementTargetRiskMonotonicity.refinement_monotone_target_risk`
