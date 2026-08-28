# Escape-Zero Completion Point

## Abstract

Faithful escape zero is equivalent to determination by the joined readout, and a unique audited parameter supplies the regularized completion point.

**Theorem 1.1 (Escape zero characterizes the audited completion point).**

$$\begin{gathered}\forall A, X, Q, Y: Type,\\{}D: A \to Type,\\{}q: X \to Q, d: \forall a: A, X \to D(a),\\{}T: X \to Y, w: \operatorname{EscapeWeight}\left(\operatorname{Prod}\left(X, X\right)\right),\\{}Cost: \forall a: A, \left(X \to D(a)\right) \to \mathbb{R}, \lambda: \mathbb{R}, a: A,\\{}(\forall S: \operatorname{Set}\left(\operatorname{Prod}\left(X, X\right)\right), \operatorname{mass}\left(w, S\right) = 0 \Leftrightarrow S = \emptyset) \Rightarrow (uniqueCompletion: \exists! \kappa: A, \operatorname{IsAuditedCompletionParameter}\left(q, d, T, w, Cost, \lambda, \kappa\right)) \Rightarrow\\{}\begin{gathered}(\operatorname{parameterEscapeDefect}\left(q, d, T, w, a\right) = 0 \Rightarrow \operatorname{FactorsThrough}\left(T, \operatorname{conceptJoin}\left(q, d(a)\right)\right)) \land\\{}(\operatorname{FactorsThrough}\left(T, \operatorname{conceptJoin}\left(q, d(a)\right)\right) \Rightarrow \operatorname{parameterEscapeDefect}\left(q, d, T, w, a\right) = 0) \land\\{}\operatorname{IsMinOn}\left(\operatorname{regularizedCompletionObjective}\left(q, d, T, w, Cost, \lambda\right), \operatorname{SetUniv}\left(A\right), \operatorname{choose}\left(uniqueCompletion\right)\right) \land\\{}\operatorname{parameterEscapeDefect}\left(q, d, T, w, \operatorname{choose}\left(uniqueCompletion\right)\right) = 0 \land\\{}\operatorname{FactorsThrough}\left(T, \operatorname{conceptJoin}\left(q, d(\operatorname{choose}\left(uniqueCompletion\right))\right)\right) \land\\{}\forall candidate: A, \operatorname{IsAuditedCompletionParameter}\left(q, d, T, w, Cost, \lambda, candidate\right) \Rightarrow candidate = \operatorname{choose}\left(uniqueCompletion\right)\end{gathered}\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Completion/EscapeZeroCompletionPoint.escape_zero_iff_determined_with_audited_minimizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A baseline readout q is joined with the parameter-dependent definition readout d(a). The escape defect is the supplied weight of target pairs that the joint readout still identifies.

Faithfulness says that a set has zero weight exactly when it is empty. The repository's sufficiency-escape equivalence then gives both directions between zero defect and target factorization through the joined readout.

An audited parameter has exactly three properties: it globally minimizes Delta(a) + lambda Cost(d(a)), its joint readout determines the target, and its escape defect is zero. Under the source's unique-existence condition, the selected witness kappa has each property and every other audited parameter equals it.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Completion/EscapeZeroCompletionPoint.escape_zero_iff_determined_with_audited_minimizer`
- Dependency: [D5/S3/AnalyticClosure/Budget/BudgetedEscapeRateAntitone](../../AnalyticClosure/Budget/BudgetedEscapeRateAntitone.md)
- Dependency: [D5/S3/ConceptDynamics/RefinementFactorization/SufficiencyEscapeEquivalence](../RefinementFactorization/SufficiencyEscapeEquivalence.md)
