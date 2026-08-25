# Commuting Target Exchange

## Abstract

Commuting state interventions have an empty target-level order-defect set.

**Definition 1.1 (Target-level intervention defect).**

Lean statement: `D5/S3/ConceptDynamics/InterventionsExchange/CommutingTargetExchange.commutationDefect`

*Formalization.* `D5/S3/ConceptDynamics/InterventionsExchange/CommutingTargetExchange.commutationDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For two state maps and a target readout, the commutation defect is the set of states whose target values differ after the two orders of composition.

**Theorem 1.2 (Commuting maps have no target defect).**

$$\forall X : Type, Y : Type,\\{}F, G: X \to X, T: X \to Y,\\{}F \circ G = G \circ F \Rightarrow\\{}\operatorname{commutationDefect}(F, G, T) = \emptyset.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InterventionsExchange/CommutingTargetExchange.commuting_target_defect_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source state carrier, two intervention maps, and target readout are independent primitives. The public premise is equality of the two composite maps.

The conclusion exposes the source Comm object directly as the empty set. It follows by applying the target to the composite-map equality pointwise.

The defect set is constructed from the two source compositions before the theorem; it is not defined as the empty target.

No exact repository theorem packages this general target-level empty defect statement. The canonical Concept carrier and elementary set equality are used directly.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InterventionsExchange/CommutingTargetExchange.commutationDefect`
- Truth anchor: `D5/S3/ConceptDynamics/InterventionsExchange/CommutingTargetExchange.commuting_target_defect_empty`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../ConceptFiberDecomposition.md)
