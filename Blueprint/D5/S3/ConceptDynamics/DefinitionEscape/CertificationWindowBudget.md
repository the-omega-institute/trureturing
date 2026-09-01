# Certification Windows under Budget

## Abstract

Finite certification windows grow with budget and are closed under union at the summed budget.

**Theorem 1.1 (Certification windows are monotone in budget).**

$$\forall I: Type, Target: Type,\\{}\Gamma: \operatorname{Set}\left(I\right), coverage: I \to \operatorname{Set}\left(Target\right),\\{}candidateCost: I \to \operatorname{NNReal},\\{}\operatorname{Monotone}\left(\operatorname{certificationWindow}\left(\Gamma, coverage, candidateCost\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscape/CertificationWindowBudget.certification_window_budget_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Candidates lie in Gamma. Each candidate has a nonnegative-real cost and covers a set of targets. A target set belongs to the certification window when one finite selection covers it and its canonical finiteSelectionCost is at most the budget.

The same finite selection witnesses certification at every larger budget. Consequently the theorem has no finiteness, coverage, positivity, or nonemptiness premise beyond the NNReal types already carried by costs and budgets.

**Theorem 1.2 (Certified target sets combine at the summed budget).**

$$\begin{aligned}\forall I: Type, Target: Type,\\{}\Gamma: \operatorname{Set}\left(I\right), coverage: I \to \operatorname{Set}\left(Target\right),\\{}candidateCost: I \to \operatorname{NNReal},\\claimA: \operatorname{Set}\left(Target\right), claimB: \operatorname{Set}\left(Target\right),\\budgetA: \operatorname{NNReal}, budgetB: \operatorname{NNReal},\\claimA \in \operatorname{certificationWindow}\left(\Gamma, coverage, candidateCost, budgetA\right) \Rightarrow claimB \in \operatorname{certificationWindow}\left(\Gamma, coverage, candidateCost, budgetB\right) \Rightarrow\\\operatorname{union}\left(claimA, claimB\right) \in \operatorname{certificationWindow}\left(\Gamma, coverage, candidateCost, budgetA + budgetB\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscape/CertificationWindowBudget.certification_window_union_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given witnesses for claimA and claimB, the union of their finite candidate selections captures the union of the target sets. Candidates present in both selections occur only once in the combined selection.

Nonnegative candidate costs make the combined selection cost at most the sum of the two original costs. This yields unconditional union closure at budgetA plus budgetB; allowing signed costs would invalidate that natural subadditivity argument.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/CertificationWindowBudget.certification_window_budget_monotone`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/CertificationWindowBudget.certification_window_union_closed`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting](FiniteCoverCounting.md)
