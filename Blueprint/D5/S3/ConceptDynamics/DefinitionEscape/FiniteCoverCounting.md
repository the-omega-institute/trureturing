# Finite Cover and Counting

## Abstract

Finite definition cuts cover residuals with diminishing capture and antitone escape.

**Theorem 1.1 (Finite residual covers control marginal capture and counting escape).**

$$(\operatorname{blindResidual}\left(\Gamma, q, T\right) = \emptyset) \Leftrightarrow \operatorname{union}\left(d \in \Gamma, \operatorname{intersection}\left(\operatorname{defectRelation}\left(q, T\right), \operatorname{complement}\left(\operatorname{conceptKernel}\left(d\right)\right)\right)\right) = \operatorname{defectRelation}\left(q, T\right),\\{}(\operatorname{blindResidual}\left(\Gamma, q, T\right) = \emptyset) \Rightarrow \operatorname{finiteSelectionSufficient}\left(\Gamma, q, T\right),\\{}\Gamma \subseteq \Delta \Rightarrow \operatorname{blindKernelReductionMeasure}\left(\Delta, q, T, d\right)_{count} \leq \operatorname{blindKernelReductionMeasure}\left(\Gamma, q, T, d\right)_{count},\\{}b_{1} \leq b_{2} \Rightarrow \operatorname{budgetedEscapeRate}\left(b_{2}\right)_{count} \leq \operatorname{budgetedEscapeRate}\left(b_{1}\right)_{count}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting.finite_cover_counting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state type is finite and inhabited. The baseline residual is the canonical defectRelation. A definition cut is written directly as the part of that residual outside the imported conceptKernel; the module introduces no second residual or public cut-set definition.

The first conjunct identifies sufficiency, represented by an empty blindResidual, with coverage by the union of all definition cuts. Mathlib finite_subset_iUnion then extracts a finite subfamily, and the accepted target recovery criterion turns its empty joined defect into finiteSelectionSufficient.

For Gamma contained in Delta, every pair blind to Delta is blind to Gamma. Set.ncard_le_ncard therefore makes the imported blind-kernel reduction measure antitone in the accumulated definition family. A Boolean example makes the inequality strict: identity capture has positive marginal from the empty family and zero after identity has already been added.

The counting escape-rate conjunct is not reproved. It instantiates the second conjunct of budgeted_escape_rate_bounds_and_antitone with finite ncard mass. Its explicit premises require a nonempty baseline defect and a feasible strategy at the smaller budget. A two-strategy Boolean probe computes rates one and zero, so reversing the budget direction produces a false inequality.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting.finite_cover_counting`
- Dependency: [D5/S3/AnalyticClosure/Budget/BudgetedEscapeRateAntitone](../../AnalyticClosure/Budget/BudgetedEscapeRateAntitone.md)
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/BlindKernelReductionMeasure](BlindKernelReductionMeasure.md)
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/ResidualJoinLaw](ResidualJoinLaw.md)
