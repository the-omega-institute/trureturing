# Judgment-Relative Analogy Criterion

## Abstract

Similarity supports equal judgments only when it preserves judgment distinctions.

**Theorem 1.1 (Relevant analogy criterion).**

$$\begin{gathered}\forall X, B, Y: \operatorname{Type},\\{}R: X \to B, J: X \to Y,\\{}(\operatorname{Refines}(\operatorname{canonicalTargetReadout}(J), R) \longrightarrow\\{}\forall x, y, R(x) = R(y) \longrightarrow J(x) = J(y)) \land\\{}((\exists x, y, R(x) = R(y) \land J(x) \neq J(y)) \longrightarrow\\{}\neg \operatorname{Refines}(\operatorname{canonicalTargetReadout}(J), R)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Governance/JudgmentRelativeAnalogyCriterion.judgment_relative_analogy_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical judgment target records exactly the distinctions made by J. If it factors through the case-similarity readout R, equal R-values force equal judgments.

A pair of cases with the same similarity value and different judgments is therefore an explicit obstruction to that factorization. Similarity is consequently assessed relative to the judgment target whose distinctions it must preserve.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Governance/JudgmentRelativeAnalogyCriterion.judgment_relative_analogy_criterion`
- Dependency: [D5/S3/ConceptDynamics/Governance/RuleConstraintDifferenceCriterion](RuleConstraintDifferenceCriterion.md)
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/UniversalSufficiencyFactorization](../Sufficiency/UniversalSufficiencyFactorization.md)
