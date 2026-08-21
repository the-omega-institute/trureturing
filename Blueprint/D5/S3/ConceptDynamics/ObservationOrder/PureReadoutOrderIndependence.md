# Pure Readouts and Observation Order

## Abstract

Identity observation updates exclude order effects from two static readouts.

**Theorem 1.1 (Pure readouts have no order effect).**

$$\forall X, C, D: \operatorname{Type}, o_{C}: X \to C, o_{D}: X \to D, p_{C}, p_{D}: X \to X, E: ApplicationDomain \to \operatorname{Prop}, (\forall a: ApplicationDomain, E(a) \Rightarrow \operatorname{hasOrderEffect}(\operatorname{forwardJoint}(o_{C}, o_{D}, p_{C}), \operatorname{reverseJoint}(o_{C}, o_{D}, p_{D}))) \Rightarrow\ ((p_{C} = id \land p_{D} = id) \Rightarrow \neg \operatorname{hasOrderEffect}(\operatorname{forwardJoint}(o_{C}, o_{D}, p_{C}), \operatorname{reverseJoint}(o_{C}, o_{D}, p_{D}))) \land\ (\forall a: ApplicationDomain, E(a) \Rightarrow p_{C} \neq id \lor p_{D} \neq id).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationOrder/PureReadoutOrderIndependence.pure_readout_order_independence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward joint readout observes C, applies its state update, and then observes D. The reverse joint readout observes D first and returns the coordinates in the same C,D order.

An order effect is witnessed by a state where those two paired results differ. Identity updates reduce both constructions to the canonical join of the two static concept readouts.

The public application domain contains quantum measurement, survey order, judicial inquiry, medical diagnosis, psychological priming, and institutional classification. Any reported effect witnessed by the source joint readouts forces at least one nonidentity update.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ObservationOrder/PureReadoutOrderIndependence.pure_readout_order_independence`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
