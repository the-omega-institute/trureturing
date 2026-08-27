# Mutual Nondisturbance and Observation Order

## Abstract

Mutual readout nondisturbance removes observation-order effects.

**Theorem 1.1 (Mutual nondisturbance removes order effects).**

$$\begin{aligned}\forall X, C, D: \operatorname{Type},\\o_{C}: X \to C, o_{D}: X \to D,\\p_{C}, p_{D}: X \to X,\\(o_{D} \circ p_{C} = o_{D} \land o_{C} \circ p_{D} = o_{C}) \Rightarrow\\(\operatorname{forwardJoint}\left(o_{C}, o_{D}, p_{C}\right) = \operatorname{reverseJoint}\left(o_{C}, o_{D}, p_{D}\right)) \land \\((p_{D} \circ p_{C} = p_{C} \circ p_{D}) \Rightarrow \forall x: X, (\operatorname{forwardJoint}\left(o_{C}, o_{D}, p_{C}, x\right), p_{D}(p_{C}(x))) = (\operatorname{reverseJoint}\left(o_{C}, o_{D}, p_{D}, x\right), p_{C}(p_{D}(x)))).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationOrder/MutualNondisturbanceOrderIndependence.mutual_nondisturbance_order_independence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ordered joint readouts are the canonical forwardJoint and reverseJoint constructions from the ObservationOrder family.

Each update preserves the other instrument's readout. These two independent equations identify the two joint readout functions.

Under the additional commutation equation, the public second clause compares the complete paired result at every state: its first coordinate is the joint readout and its second is the final state.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ObservationOrder/MutualNondisturbanceOrderIndependence.mutual_nondisturbance_order_independence`
- Dependency: [D5/S3/ConceptDynamics/ObservationOrder/PureReadoutOrderIndependence](PureReadoutOrderIndependence.md)
