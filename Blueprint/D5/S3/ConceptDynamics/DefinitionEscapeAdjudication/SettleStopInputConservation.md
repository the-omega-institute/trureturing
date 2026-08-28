# Settle Stop Input Conservation

## Abstract

The stop component of settlement is conserved by equal decision and orientation inputs.

**Theorem 1.1 (Settlement stop depends only on the sealed decision and orientation).**

$$\forall K, KPrime: \operatorname{ProspectiveCommitment}\left(n\right),\\{}O, OPrime: \operatorname{OrientationSpec}\left(AdmTarget, InScope\right),\\{}(\operatorname{decision}\left(K\right) = \operatorname{decision}\left(KPrime\right) \land O = OPrime) \Rightarrow\\{}\operatorname{settleStop}\left(AdmTarget, InScope, O, K\right) = \operatorname{settleStop}\left(AdmTarget, InScope, OPrime, KPrime\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/SettleStopInputConservation.settle_stop_depends_only_on_decision_and_orientation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two commitments have the same round and the same canonical prospective-commitment type. The two sourced orientations also share one orientation type and its admissible target and scope.

Under the decidable premises carried by the frozen finite checker, equality of the sealed decision fields and orientations preserves the Boolean settlement stop result.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/SettleStopInputConservation.settle_stop_depends_only_on_decision_and_orientation`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/AdjudicationStopTargetCorrectness](AdjudicationStopTargetCorrectness.md)
