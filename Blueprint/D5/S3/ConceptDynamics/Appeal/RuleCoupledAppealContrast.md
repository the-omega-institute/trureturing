# Rule-Coupled Appeal Contrast

## Abstract

An appeal computed from the case and hidden rule can recover the target even when the explanation log cannot recover that rule.

**Theorem 1.1 (Contestability need not provide rule explanation).**

$$\exists R \in \operatorname{Concept}\left((Bool \times Bool), Bool\right), L \in \operatorname{Concept}\left((Bool \times Bool), Unit\right), C \in \operatorname{Concept}\left((Bool \times Bool), Bool\right), appealOracle \in (Bool \times Bool) \to Bool, targetOracle \in (Bool \times Bool) \to Bool,\; appealOracle \circ \operatorname{conceptJoin}\left(R, C\right) = targetOracle \circ \operatorname{conceptJoin}\left(C, R\right) \land \left(\operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(targetOracle \circ \operatorname{conceptJoin}\left(C, R\right)\right), \operatorname{conceptJoin}\left(C, appealOracle \circ \operatorname{conceptJoin}\left(R, C\right)\right)\right) \land \left(\neg \operatorname{Refines}\left(R, L\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Appeal/RuleCoupledAppealContrast.rule_coupled_appeal_can_repair_without_log_explanation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The appeal oracle reads the joined rule and case coordinates, while the target oracle reads the same coordinates in the opposite order. The Boolean construction depends on both coordinates and proves the two resulting readouts equal.

Joining the case readout with that constructed appeal recovers the canonical target readout. The same nonconstant rule used by both constructions still cannot factor through the constant explanation log.

The appeal-target equality, target recovery, and missing explanation are therefore three public clauses of one shared countermodel.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Appeal/RuleCoupledAppealContrast.rule_coupled_appeal_can_repair_without_log_explanation`
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/UniversalSufficiencyFactorization](../Sufficiency/UniversalSufficiencyFactorization.md)
