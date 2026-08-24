# Finite Cover and Counting

## Abstract

Finite definition cuts cover residuals with diminishing capture and antitone escape.

**Theorem 1.1 (Finite residual covers control marginal capture and counting escape).**

$$(\operatorname{intersection}\left(\operatorname{defectRelation}\left(q, T\right), \operatorname{jointKernel}\left(\Gamma, d_{i}\right)\right) = \emptyset) \Leftrightarrow \operatorname{union}\left(d \in \Gamma, \operatorname{intersection}\left(\operatorname{defectRelation}\left(q, T\right), \operatorname{complement}\left(\operatorname{conceptKernel}\left(d\right)\right)\right)\right) = \operatorname{defectRelation}\left(q, T\right),\\{}(\operatorname{intersection}\left(\operatorname{defectRelation}\left(q, T\right), \operatorname{jointKernel}\left(\Gamma, d_{i}\right)\right) = \emptyset) \Rightarrow \operatorname{finiteSelectionSufficientOnRange}\left(\Gamma, d_{i}, q, T\right),\\{}(\Gamma \subseteq \Delta \land \neg(d \in \Delta)) \Rightarrow \operatorname{nu}\left(\operatorname{intersection}\left(\operatorname{intersection}\left(\operatorname{defectRelation}\left(q, T\right), \operatorname{jointKernel}\left(\Delta, d_{i}\right)\right), \operatorname{complement}\left(\operatorname{conceptKernel}\left(d\right)\right)\right)\right) \leq \operatorname{nu}\left(\operatorname{intersection}\left(\operatorname{intersection}\left(\operatorname{defectRelation}\left(q, T\right), \operatorname{jointKernel}\left(\Gamma, d_{i}\right)\right), \operatorname{complement}\left(\operatorname{conceptKernel}\left(d\right)\right)\right)\right),\\{}\left(\left(\operatorname{Nonempty}\left(\operatorname{defectRelation}\left(q, T\right)\right) \land (\exists s \in Strategy,\; \operatorname{cost}\left(s\right) \le b_{1})\right) \land b_{1} \le b_{2}\right) \Rightarrow \operatorname{budgetedEscapeRate}\left(b_{2}\right)_{count} \le \operatorname{budgetedEscapeRate}\left(b_{1}\right)_{count}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting.finite_cover_counting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state type is finite; it need not be inhabited. Candidate definitions are indexed by I with a dependent codomain family V : I -> Type and readouts d_i : X -> V(i). Gamma and Delta are index sets, and the imported dependent jointKernel is used directly. The supplement in the counting clause has its own unrelated codomain.

The first conjunct identifies an empty target defect intersected with the dependent family joint kernel with coverage by all definition cuts. Mathlib finite_subset_iUnion extracts a finite subfamily. The second conjunct constructs recovery only on Set.range of that finite joint readout, so it also holds for an empty state and empty target; the stronger whole-codomain recovery requirement is false there.

For Gamma contained in Delta and a fresh candidate d, every pair blind to Delta is blind to Gamma. Monotonicity of the parameter nu therefore makes weighted marginal capture antitone in the accumulated family. A Boolean witness uses a non-counting point weight of three: negation removes the weighted pair before identity arrives, so capture falls strictly and the reversed inequality is false.

Only the fourth conjunct is specialized to counting. It instantiates the second conjunct of budgeted_escape_rate_bounds_and_antitone with finite ncard mass. Its explicit premises require a nonempty baseline defect and a feasible strategy at the smaller budget. A two-strategy Boolean probe computes rates one and zero, so reversing the budget direction produces a false inequality.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting.finite_cover_counting`
- Dependency: [D5/S3/AnalyticClosure/Budget/BudgetedEscapeRateAntitone](../../AnalyticClosure/Budget/BudgetedEscapeRateAntitone.md)
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/BlindKernelObstruction](BlindKernelObstruction.md)
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/ResidualJoinLaw](ResidualJoinLaw.md)
