# Finite Cover and Counting

## Abstract

The two residual-cover clauses and counting antitonicity are proved; marginal capture needs a stronger weight interface.

**Theorem 1.1 (Finite cover and counting package).**

$$[\operatorname{Finite}(X)], [\operatorname{DecidableEq}(I)],\\\forall A, \operatorname{mass}\left(countingWeight, A\right) = \operatorname{ncard}\left(A\right),\\((\operatorname{intersection}\left(\operatorname{defectRelation}\left(q, T\right), \operatorname{jointKernel}\left(\Gamma, d_{i}\right)\right) = \emptyset) \Leftrightarrow \operatorname{union}\left(d \in \Gamma, \operatorname{intersection}\left(\operatorname{defectRelation}\left(q, T\right), \operatorname{complement}\left(\operatorname{conceptKernel}\left(d\right)\right)\right)\right) = \operatorname{defectRelation}\left(q, T\right)) \land \left(\left(\left(\operatorname{Finite}\left(X\right) \land \operatorname{intersection}\left(\operatorname{defectRelation}\left(q, T\right), \operatorname{jointKernel}\left(\Gamma, d_{i}\right)\right) = \emptyset\right) \Rightarrow \operatorname{finiteSelectionSufficientOnRange}\left(\Gamma, d_{i}, q, T\right)\right) \land \left(\left((\forall d \in I,\; d \in \Gamma \Rightarrow 0 \le \operatorname{c}\left(d\right)) \land \left(0 \le b_{1} \land \left(b_{1} \le b_{2} \land 0 < \operatorname{mass}\left(countingWeight, \operatorname{defectRelation}\left(q, T\right)\right)\right)\right)\right) \Rightarrow \operatorname{budgetedEscapeRate}\left(q, \operatorname{finiteSelectionSupplement}\left(\Gamma, d_{i}\right), T, \operatorname{finiteSelectionCost}\left(\Gamma, c\right), countingWeight, b_{2}\right) \le \operatorname{budgetedEscapeRate}\left(q, \operatorname{finiteSelectionSupplement}\left(\Gamma, d_{i}\right), T, \operatorname{finiteSelectionCost}\left(\Gamma, c\right), countingWeight, b_{1}\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting.finite_cover_counting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Candidate definitions are indexed by I with dependent codomains V(i). The packaged theorem has the Lean instances Finite X and DecidableEq I. Its first conjunct is general in X; the second retains the explicit Finite X premise used by finite_subset_iUnion to extract a finite subfamily.

finiteSelectionSufficientOnRange is the canonical Refines target relation against Set.rangeFactorization of the selected joint readout. The proof reuses inductive_sufficiency_criterion. The third conjunct is backed by counting_escape_antitone_law.

**Definition 1.2 (CAS marginal-capture statement).**

$$\left(\Gamma \subseteq \Delta \land \neg(d \in \Delta)\right) \Rightarrow \operatorname{capturedEscapeMass}\left(\operatorname{union}\left(\Gamma, \{d\}\right), d_{i}, q, T, nu\right) - \operatorname{capturedEscapeMass}\left(\Gamma, d_{i}, q, T, nu\right) \ge \operatorname{capturedEscapeMass}\left(\operatorname{union}\left(\Delta, \{d\}\right), d_{i}, q, T, nu\right) - \operatorname{capturedEscapeMass}\left(\Delta, d_{i}, q, T, nu\right).$$

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting.marginalCaptureLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This Prop uses the two CAS definitions directly: residualEscapeMass(S) is M(S) = nu.mass(E(q join S; T)), and capturedEscapeMass(S) is F(S) = M(empty) - M(S). Gamma is contained in Delta and d is fresh for Delta. The theorem marginal_capture_law_not_implied_by_escape_weight gives a counterexample inside this weak Lean interface. Identifying the difference with a weighted union of cuts needs additivity, and the source's diminishing-returns argument needs the stronger measure semantics not carried by EscapeWeight.

**Theorem 1.3 (CAS counting escape-rate theorem).**

$$[\operatorname{Finite}(X)], [\operatorname{DecidableEq}(I)],\\\forall A, \operatorname{mass}\left(countingWeight, A\right) = \operatorname{ncard}\left(A\right),\\\left((\forall d \in I,\; d \in \Gamma \Rightarrow 0 \le \operatorname{c}\left(d\right)) \land \left(0 \le b_{1} \land \left(b_{1} \le b_{2} \land 0 < \operatorname{mass}\left(countingWeight, \operatorname{defectRelation}\left(q, T\right)\right)\right)\right)\right) \Rightarrow \operatorname{budgetedEscapeRate}\left(q, \operatorname{finiteSelectionSupplement}\left(\Gamma, d_{i}\right), T, \operatorname{finiteSelectionCost}\left(\Gamma, c\right), countingWeight, b_{2}\right) \le \operatorname{budgetedEscapeRate}\left(q, \operatorname{finiteSelectionSupplement}\left(\Gamma, d_{i}\right), T, \operatorname{finiteSelectionCost}\left(\Gamma, c\right), countingWeight, b_{1}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting.counting_escape_antitone_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This Prop uses CAS strategies Finset Gamma, finiteSelectionSupplement, and finiteSelectionCost(S) = sum d in S, c(d). Candidate costs and b1 are nonnegative, so the empty selection has cost zero and is feasible; b1 <= b2 gives the displayed antitone direction. Every budgetedEscapeRate occurrence names q, the supplement, T, the summed cost, countingWeight, and its budget. Here countingWeight is the concrete Lean weight mass(A) = ncard(A), under Finite X and DecidableEq I. The empty selection proves feasibility at b1, and the generic budget theorem then gives the result.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting.counting_escape_antitone_law`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting.finite_cover_counting`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting.marginalCaptureLaw`
- Dependency: [D5/S3/AnalyticClosure/Budget/BudgetedEscapeRateAntitone](../../AnalyticClosure/Budget/BudgetedEscapeRateAntitone.md)
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/BlindKernelObstruction](BlindKernelObstruction.md)
- Dependency: [D5/S3/ConceptDynamics/Refinement/InductiveSufficiency](../Refinement/InductiveSufficiency.md)
