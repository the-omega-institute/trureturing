# Complete History-Sensitive Outcome Reduction

## Abstract

History sensitivity obstructs outcome reduction and identifies the kernel defect.

**Theorem 1.1 (History sensitivity obstructs reduction and exposes its defect).**

$$\forall Gamma, X, L: \operatorname{Type},\\{}e: Gamma \to X, J: Gamma \to L,\\{}{\exists gamma, gammaPrime: Gamma, e(gamma) = e(gammaPrime) \land J(gamma) \neq J(gammaPrime)} \Rightarrow\\{}(\neg {\exists \overline{J}: X \to L, J = \operatorname{compose}(\overline{J}, e)}) \land\\{}\operatorname{defectRelation}(e, J) = \ker e \setminus \ker J.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/NormativeStructure/HistorySensitiveOutcomeReductionComplete.history_sensitive_evaluation_not_outcome_reducible_with_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The path type, endpoint readout, and normative evaluation are independent source primitives on the canonical concept carrier.

The first public conjunct is the frozen obstruction theorem: two paths with one endpoint and different evaluations preclude an endpoint-only factorization.

The second conjunct identifies the canonical defect relation with the set difference of the endpoint and evaluation equality kernels. The repository's defectRelation primitive is imported rather than redeclared.

The source's normative list and its informal interpretation are qualitative remarks without an in-scope predicate; they are outside the displayed formal theorem.

## References

- Truth anchor: `D5/S3/ConceptDynamics/NormativeStructure/HistorySensitiveOutcomeReductionComplete.history_sensitive_evaluation_not_outcome_reducible_with_defect`
- Dependency: [D5/S3/ConceptDynamics/NormativeStructure/HistorySensitiveOutcomeReductionObstruction](HistorySensitiveOutcomeReductionObstruction.md)
- Dependency: [D5/S3/ConceptDynamics/TargetRisk/RefinementRiskCostTradeoff](../TargetRisk/RefinementRiskCostTradeoff.md)
