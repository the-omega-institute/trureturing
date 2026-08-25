# Finite Cover and Counting

## Abstract

The two residual-cover clauses and counting antitonicity are proved; marginal capture needs a stronger weight interface.

**Theorem 1.1 (Finite cover and counting package).**

$$((\operatorname{intersection}\left(\operatorname{defectRelation}\left(q, T\right), \operatorname{jointKernel}\left(\Gamma, d_{i}\right)\right) = \emptyset) \Leftrightarrow \operatorname{union}\left(d \in \Gamma, \operatorname{intersection}\left(\operatorname{defectRelation}\left(q, T\right), \operatorname{complement}\left(\operatorname{conceptKernel}\left(d\right)\right)\right)\right) = \operatorname{defectRelation}\left(q, T\right)) \land \left(\left(\left(\operatorname{Finite}\left(X\right) \land \operatorname{intersection}\left(\operatorname{defectRelation}\left(q, T\right), \operatorname{jointKernel}\left(\Gamma, d_{i}\right)\right) = \emptyset\right) \Rightarrow \operatorname{finiteSelectionSufficientOnRange}\left(\Gamma, d_{i}, q, T\right)\right) \land b_{1}, b_{2}: \operatorname{NNReal},\\\forall A, \operatorname{mass}\left(countingWeight, A\right) = \operatorname{ncard}\left(A\right),\\0 < \operatorname{mass}\left(countingWeight, \operatorname{defectRelation}\left(q, T\right)\right) \Rightarrow \left(b_{1} \le b_{2} \Rightarrow \operatorname{budgetedEscapeRate}\left(q, \operatorname{finiteSelectionSupplement}\left(\Gamma, d_{i}\right), T, \operatorname{finiteSelectionCost}\left(\Gamma, c\right), countingWeight, b_{2}\right) \le \operatorname{budgetedEscapeRate}\left(q, \operatorname{finiteSelectionSupplement}\left(\Gamma, d_{i}\right), T, \operatorname{finiteSelectionCost}\left(\Gamma, c\right), countingWeight, b_{1}\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting.finite_cover_counting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Candidate definitions are indexed by I with dependent codomains V(i). The packaged theorem has no global instances. Its first conjunct is general in X and I. The second retains the explicit Finite X premise used by finite_subset_iUnion to extract a finite subfamily.

finiteSelectionSufficientOnRange is the canonical Refines target relation against Set.rangeFactorization of the selected joint readout. The proof reuses inductive_sufficiency_criterion. The third conjunct is backed directly by counting_escape_antitone_law, without a finite-X premise. finiteSelectionSupplement chooses classical equality only inside its Finset implementation, so no public declaration requires DecidableEq I.

**Theorem 1.2 (Finite residual-cover laws).**

$$\begin{aligned}\forall I: \operatorname{Type}, X: \operatorname{Type}, C: \operatorname{Type}, Target: \operatorname{Type},\\V: I \to \operatorname{Type},\\\Gamma: \operatorname{Set}\left(I\right),\\definitions: \forall i: I, \operatorname{Concept}\left(X, V(i)\right),\\q: \operatorname{Concept}\left(X, C\right), target: \operatorname{Concept}\left(X, Target\right),\\((\operatorname{intersection}\left(\operatorname{defectRelation}\left(q, target\right), \operatorname{jointKernel}\left(\Gamma, definitions\right)\right) = \emptyset) \Leftrightarrow \operatorname{union}\left(d \in \Gamma, \operatorname{intersection}\left(\operatorname{defectRelation}\left(q, target\right), \operatorname{complement}\left(\operatorname{conceptKernel}\left(definitions, d\right)\right)\right)\right) = \operatorname{defectRelation}\left(q, target\right)) \land \left(\left(\operatorname{Finite}\left(X\right) \land \operatorname{intersection}\left(\operatorname{defectRelation}\left(q, target\right), \operatorname{jointKernel}\left(\Gamma, definitions\right)\right) = \emptyset\right) \Rightarrow \operatorname{finiteSelectionSufficientOnRange}\left(\Gamma, definitions, q, target\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting.finite_cover_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The index, state, concept-output, and target-output carriers are explicit Type binders. V is the dependent codomain family over I; Gamma, definitions, q, and target retain the types displayed by the Lean declaration.

The first clause identifies joint-kernel blindness with coverage by the candidate cuts. The second keeps Finite X local to the premise that extracts a finite sufficient subfamily.

**Definition 1.3 (CAS marginal-capture statement).**

$$\left(\Gamma \subseteq \Delta \land \neg(d \in \Delta)\right) \Rightarrow \operatorname{capturedEscapeMass}\left(\operatorname{union}\left(\Gamma, \{d\}\right), d_{i}, q, T, nu\right) - \operatorname{capturedEscapeMass}\left(\Gamma, d_{i}, q, T, nu\right) \ge \operatorname{capturedEscapeMass}\left(\operatorname{union}\left(\Delta, \{d\}\right), d_{i}, q, T, nu\right) - \operatorname{capturedEscapeMass}\left(\Delta, d_{i}, q, T, nu\right).$$

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting.marginalCaptureLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This Prop uses the two CAS definitions directly: residualEscapeMass(S) is M(S) = nu.mass(E(q join S; T)), and capturedEscapeMass(S) is F(S) = M(empty) - M(S). Gamma is contained in Delta and d is fresh for Delta. The theorem marginal_capture_law_not_implied_by_escape_weight gives a counterexample inside this weak Lean interface. Identifying the difference with a weighted union of cuts needs additivity, and the source's diminishing-returns argument needs the stronger measure semantics not carried by EscapeWeight.

**Theorem 1.4 (CAS counting escape-rate theorem).**

$$b_{1}, b_{2}: \operatorname{NNReal},\\\forall A, \operatorname{mass}\left(countingWeight, A\right) = \operatorname{ncard}\left(A\right),\\0 < \operatorname{mass}\left(countingWeight, \operatorname{defectRelation}\left(q, T\right)\right) \Rightarrow \left(b_{1} \le b_{2} \Rightarrow \operatorname{budgetedEscapeRate}\left(q, \operatorname{finiteSelectionSupplement}\left(\Gamma, d_{i}\right), T, \operatorname{finiteSelectionCost}\left(\Gamma, c\right), countingWeight, b_{2}\right) \le \operatorname{budgetedEscapeRate}\left(q, \operatorname{finiteSelectionSupplement}\left(\Gamma, d_{i}\right), T, \operatorname{finiteSelectionCost}\left(\Gamma, c\right), countingWeight, b_{1}\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting.counting_escape_antitone_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This theorem uses CAS strategies Finset Gamma, finiteSelectionSupplement, and finiteSelectionCost(S) = sum d in S, c(d). Budgets b1 and b2 inhabit NNReal, while candidate costs remain arbitrary real values. The empty selection therefore has cost zero and is feasible at b1; b1 <= b2 gives the displayed antitone direction. Every budgetedEscapeRate occurrence names q, the supplement, T, the summed cost, countingWeight, and its budget. Here countingWeight is the concrete Lean weight mass(A) = ncard(A), with no finiteness assumption on X; positive baseline mass locally proves that the baseline defect is finite. Finite-set membership equality is chosen internally. The generic budget theorem then gives the non-strict direction rate(b2) <= rate(b1). Thus the sole CAS premise is positive baseline mass; budget order is the condition of the antitone implication, not an extra model assumption. A constant candidate is an elaborating false neighbor for strict decrease, while an identity candidate gives a strict nontrivial model with rate(1) < rate(0).

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting.counting_escape_antitone_law`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting.finite_cover_counting`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting.finite_cover_laws`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting.marginalCaptureLaw`
- Dependency: [D5/S3/AnalyticClosure/Budget/BudgetedEscapeRateAntitone](../../AnalyticClosure/Budget/BudgetedEscapeRateAntitone.md)
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/BlindKernelObstruction](BlindKernelObstruction.md)
- Dependency: [D5/S3/ConceptDynamics/Refinement/InductiveSufficiency](../Refinement/InductiveSufficiency.md)
