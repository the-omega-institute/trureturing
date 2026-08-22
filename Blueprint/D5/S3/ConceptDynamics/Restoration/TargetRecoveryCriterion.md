# Target Recovery Criterion

## Abstract

A process preserves a target exactly when it creates no target-sensitive fiber defect.

**Theorem 1.1 (Recovery is equivalent to absence of a target defect).**

$$\forall X, Y, Z: \operatorname{Type},\\{}[\operatorname{Nonempty}(X)], U: X \to Y, T: X \to Z,\\{}(\exists r: Y \to Z, T = r \circ U \Leftrightarrow \forall x, y: X, U(x) = U(y) \Rightarrow T(x) = T(y)) \land\\{}(\forall x, y: X, U(x) = U(y) \Rightarrow T(x) = T(y) \Leftrightarrow \operatorname{defectRelation}\left(U, T\right) = \emptyset) \land\\{}(\operatorname{defectRelation}\left(U, T\right) = \emptyset \Leftrightarrow \exists r: Y \to Z, T = r \circ U) \land\\{}(\neg (\exists r: Y \to Z, T = r \circ U) \Leftrightarrow \operatorname{Nonempty}\left(\operatorname{defectRelation}\left(U, T\right)\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.target_recovery_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let U be a process readout and T the target to recover. The inhabited state premise supplies a target value for extending a factor map to process outputs outside the realized range.

The defect relation is constructed from U and T. It contains exactly the pairs merged by U but separated by T, so its nonemptiness is the public witness that recovery fails.

The accepted answerability criterion supplies all three positive equivalences and directly applies the pinned whole-codomain factorization theorem. Negating its empty-defect equivalence gives the final merged-state characterization.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.target_recovery_criterion`
- Dependency: [D5/S0/Rewriting/Quotients/AnswerabilityCriterion](../../../S0/Rewriting/Quotients/AnswerabilityCriterion.md)
- Dependency: [D5/S3/ConceptDynamics/TargetRisk/RefinementRiskCostTradeoff](../TargetRisk/RefinementRiskCostTradeoff.md)
