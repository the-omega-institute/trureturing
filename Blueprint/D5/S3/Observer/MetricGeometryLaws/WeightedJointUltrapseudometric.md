# Weighted Joint Ultrapseudometric and Zero Kernel

## Abstract

Weighted joint observation distance has a strong triangle law, an exact kernel, and a separated quotient.

**Definition 1.1 (Selected readouts form one joint observation).**

Lean statement: `D5/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric.selectedJointReadout`

*Formalization.* `D5/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric.selectedJointReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite budget J restricts the canonical dependent jointReadout to the selected coordinates. This is the formal q_J from the source.

**Definition 1.2 (Joint observation equality defines the kernel relation).**

Lean statement: `D5/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric.jointObservationSetoid`

*Formalization.* `D5/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric.jointObservationSetoid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The observation relation is the kernel Setoid of the selected joint readout, so related states have every selected coordinate equal.

**Definition 1.3 (The observation quotient identifies the joint kernel).**

Lean statement: `D5/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric.JointObservationQuotient`

*Formalization.* `D5/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric.JointObservationQuotient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Quotienting by the joint observation Setoid gives the carrier on which zero distance will separate equivalence classes.

**Theorem 1.4 (Nonnegative weights give the strong triangle inequality).**

$$\forall i\in J, 0 \leq w(i) \Rightarrow\\\forall x, y, z, d_{J}(x, z) \leq \max(d_{J}(x, y), d_{J}(y, z)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric.weighted_joint_ultrapseudometric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonempty budget, Finset.sup'_le reduces the claim to one coordinate. The discrete strong triangle law is multiplied by the nonnegative coordinate weight, and Finset.le_sup' embeds both resulting terms into their joint suprema.

The empty budget has distance zero. Nonnegativity is explicit because the source omits it even though multiplication by a negative weight reverses the required order.

**Theorem 1.5 (Zero distance is equality of every selected readout).**

$$\forall i\in J, 0 < w(i) \Rightarrow\\\forall x, y, d_{J}(x, y) = 0 \iff \forall i\in J, q(i, x) = q(i, y).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric.weighted_joint_zero_distance_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strict positivity makes every unequal selected coordinate contribute a positive term, so a zero supremum forces coordinate equality.

Conversely, coordinate equality makes every term zero. The result also covers an empty index type or empty budget, where both sides are vacuously zero or true.

**Theorem 1.6 (A negative weight breaks the strong triangle law).**

$$\exists i\in J, w(i) < 0 \land \neg{d_{J}(false, false) \leq \max(d_{J}(false, true), d_{J}(true, false))}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric.nonnegative_weights_are_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a singleton Unit budget with weight minus one and identity Boolean readout, the path false, true, false makes the claimed inequality reduce to zero less than or equal to minus one.

**Theorem 1.7 (A zero weight breaks the zero kernel).**

$$\exists i\in J, w(i) = 0 \land d_{J}(false, true) = 0 \land q(i, false) \neq q(i, true).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric.strictly_positive_weights_are_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A singleton coordinate of weight zero assigns distance zero to the distinct Boolean states false and true. Nonnegativity therefore does not suffice for the zero-kernel equivalence.

**Theorem 1.8 (The distance is independent of representatives).**

$$q_{J}(x) = q_{J}(x') \land q_{J}(y) = q_{J}(y') \Rightarrow\\d_{J}(x, y) = d_{J}(x', y').$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric.weighted_joint_quotient_well_defined` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Changing either state without changing any selected readout leaves every term in the finite supremum unchanged. This descent needs no sign condition on the weights.

**Definition 1.9 (Weighted distance descends to the observation quotient).**

Lean statement: `D5/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric.quotientWeightedJointDistance`

*Formalization.* `D5/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric.quotientWeightedJointDistance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Quotient.liftOn2 applies the representative-invariance theorem to define a real-valued distance directly on two observation classes.

**Theorem 1.10 (Zero quotient distance implies equality).**

$$\forall i\in J, 0 < w(i) \Rightarrow\\d_{quot}(u, v) = 0 \Rightarrow u = v.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric.quotient_weighted_joint_zero_implies_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive weights turn zero representative distance into equality of the selected joint readouts, and Quotient.sound turns that kernel relation into equality of classes. No global MetricSpace instance is installed because this module records only descent and separation.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric.JointObservationQuotient`
- Truth anchor: `D5/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric.jointObservationSetoid`
- Truth anchor: `D5/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric.nonnegative_weights_are_necessary`
- Truth anchor: `D5/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric.quotientWeightedJointDistance`
- Truth anchor: `D5/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric.quotient_weighted_joint_zero_implies_eq`
- Truth anchor: `D5/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric.selectedJointReadout`
- Truth anchor: `D5/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric.strictly_positive_weights_are_necessary`
- Truth anchor: `D5/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric.weighted_joint_quotient_well_defined`
- Truth anchor: `D5/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric.weighted_joint_ultrapseudometric`
- Truth anchor: `D5/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric.weighted_joint_zero_distance_iff`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../../ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion.md)
- Dependency: [D5/S3/Observer/MetricGeometryLaws/WeightedPredictionZeroKernel](WeightedPredictionZeroKernel.md)
