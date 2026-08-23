# Budgeted Escape Rate Bounds and Antitonicity

## Abstract

Budgeted escape rates lie in the unit interval and are antitone in budget.

**Theorem 1.1 (Budgeted escape rates are bounded and antitone).**

$$\begin{gathered}0 \le \rho_{\Gamma}(L) \le 1,\\L_{1} \le L_{2} \Rightarrow \rho_{\Gamma}(L_{2}) \le \rho_{\Gamma}(L_{1}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/Budget/BudgetedEscapeRateAntitone.budgeted_escape_rate_bounds_and_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A supplement strategy is feasible at budget L when its cost is at most L. Its escape value is the mass assigned to the canonical target-defect relation of the joined base and supplement readout, divided by the positive total mass M0. The budgeted escape rate is the real infimum of these feasible normalized values.

Nonnegative escape mass bounded above by M0 places every normalized feasible value in the unit interval. Nonemptiness and bounded-below hypotheses for the relevant value sets are explicit in the Lean declaration, so the real infima carry no hidden empty-set convention.

When L1 is at most L2, every strategy feasible at L1 is feasible at L2. The larger value set therefore has an infimum no greater than the smaller value set, which gives the asserted antitonicity.

## References

- Truth anchor: `D5/S3/AnalyticClosure/Budget/BudgetedEscapeRateAntitone.budgeted_escape_rate_bounds_and_antitone`
- Dependency: [D5/S3/ConceptDynamics/TargetRisk/RefinementRiskCostTradeoff](../../ConceptDynamics/TargetRisk/RefinementRiskCostTradeoff.md)
