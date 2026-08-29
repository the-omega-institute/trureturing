# Local-Global Residual and Target Expressibility

## Abstract

The local-global target residual is empty exactly for expressible targets.

**Definition 1.1 (The residual collects locally merged but target-separated pairs).**

$$LGRes\left(T, q\right) = (x, y) \forall i, \left(q_{i}\right)\left(x\right) = \left(q_{i}\right)\left(y\right) \land T\left(x\right) \ne T\left(y\right)$$

*Formalization.* `D5/S3/ConceptDynamics/TargetRisk/LocalGlobalResidualExpressibility.localGlobalResidual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The local-global residual of a target against a family of local readouts is the set of state pairs that every local readout merges while the target separates them. It reuses the canonical defect relation rather than introducing a second definition.

**Theorem 1.2 (Emptiness of the residual characterises expressibility).**

$$LGRes\left(T, q\right) = \emptyset \Leftrightarrow Refines\left(T, effectiveReadout\left(q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/TargetRisk/LocalGlobalResidualExpressibility.local_global_residual_empty_iff_expressible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The residual is empty precisely when the target refines the effective joint readout, that is, when the target is expressible from the local observations alone.

The proof applies the complete-observation expressibility equivalence already available in the repository instead of reproving it.

## References

- Truth anchor: `D5/S3/ConceptDynamics/TargetRisk/LocalGlobalResidualExpressibility.localGlobalResidual`
- Truth anchor: `D5/S3/ConceptDynamics/TargetRisk/LocalGlobalResidualExpressibility.local_global_residual_empty_iff_expressible`
- Dependency: [D5/S3/ConceptDynamics/RefinementFactorization/CompleteObservationExpressibilityCriterion](../RefinementFactorization/CompleteObservationExpressibilityCriterion.md)
- Dependency: [D5/S3/ConceptDynamics/TargetRisk/RefinementRiskCostTradeoff](RefinementRiskCostTradeoff.md)
