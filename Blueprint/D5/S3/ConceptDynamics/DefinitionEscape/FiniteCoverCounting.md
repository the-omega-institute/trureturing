# Finite Cover and Counting

## Abstract

Definition cuts cover residuals; two further CAS laws expose missing premises.

**Theorem 1.1 (Cut coverage and finite extraction).**

$$(\operatorname{intersection}\left(\operatorname{defectRelation}\left(q, T\right), \operatorname{jointKernel}\left(\Gamma, d_{i}\right)\right) = \emptyset) \Leftrightarrow \operatorname{union}\left(d \in \Gamma, \operatorname{intersection}\left(\operatorname{defectRelation}\left(q, T\right), \operatorname{complement}\left(\operatorname{conceptKernel}\left(d\right)\right)\right)\right) = \operatorname{defectRelation}\left(q, T\right),\\{}\left(\operatorname{Finite}\left(X\right) \land \operatorname{intersection}\left(\operatorname{defectRelation}\left(q, T\right), \operatorname{jointKernel}\left(\Gamma, d_{i}\right)\right) = \emptyset\right) \Rightarrow \operatorname{finiteSelectionSufficientOnRange}\left(\Gamma, d_{i}, q, T\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting.finite_cover_counting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Candidate definitions are indexed by I with dependent codomains V(i). The first conjunct is general in X. Only the second conjunct lists Finite X, exactly where finite_subset_iUnion is used to extract a finite subfamily.

finiteSelectionSufficientOnRange is the canonical Refines target relation against Set.rangeFactorization of the selected joint readout. The proof reuses inductive_sufficiency_criterion.

**Definition 1.2 (CAS marginal-capture statement).**

$$\left(\Gamma \subseteq \Delta \land \neg(d \in \Delta)\right) \Rightarrow \operatorname{mass}\left(nu, \operatorname{capturedPairs}\left(\operatorname{union}\left(\Gamma, \{d\}\right), d_{i}, q, T\right)\right) - \operatorname{mass}\left(nu, \operatorname{capturedPairs}\left(\Gamma, d_{i}, q, T\right)\right) \ge \operatorname{mass}\left(nu, \operatorname{capturedPairs}\left(\operatorname{union}\left(\Delta, \{d\}\right), d_{i}, q, T\right)\right) - \operatorname{mass}\left(nu, \operatorname{capturedPairs}\left(\Delta, d_{i}, q, T\right)\right).$$

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting.marginalCaptureLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This Prop records the exact DECT section 4.4 difference formula: F(S) is nu.mass of capturedPairs(S), Gamma is contained in Delta, and d is fresh for Delta. It is not claimed as a theorem. EscapeWeight has only zero-empty and nonnegative laws; a checked counterexample shows that these do not imply the displayed diminishing return.

**Definition 1.3 (CAS counting escape-rate statement).**

$$\left(0 < \operatorname{ncard}\left(\operatorname{defectRelation}\left(q, T\right)\right) \land b_{1} \le b_{2}\right) \Rightarrow \operatorname{budgetedEscapeRate}\left(b_{2}\right)_{count} \le \operatorname{budgetedEscapeRate}\left(b_{1}\right)_{count}.$$

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting.countingEscapeAntitoneLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This Prop keeps only the source premises: positive baseline counting mass and b1 <= b2. It is not claimed as a theorem. With no strategy feasible at b1, the current Real.sInf encoding gives rate(b1)=0, and a checked example falsifies the displayed direction.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting.countingEscapeAntitoneLaw`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting.finite_cover_counting`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting.marginalCaptureLaw`
- Dependency: [D5/S3/AnalyticClosure/Budget/BudgetedEscapeRateAntitone](../../AnalyticClosure/Budget/BudgetedEscapeRateAntitone.md)
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/BlindKernelObstruction](BlindKernelObstruction.md)
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/ResidualJoinLaw](ResidualJoinLaw.md)
- Dependency: [D5/S3/ConceptDynamics/Refinement/InductiveSufficiency](../Refinement/InductiveSufficiency.md)
