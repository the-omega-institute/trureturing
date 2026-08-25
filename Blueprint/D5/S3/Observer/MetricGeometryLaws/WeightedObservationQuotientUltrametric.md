# Weighted Observation-Quotient Ultrametric

## Abstract

Positive weighted equality readouts descend to a genuine observation-quotient ultrametric.

**Theorem 1.1 (Zero distance is exactly equality on the observation quotient).**

$$\forall I, X: Type, O: I \to Type,\\{}J: \operatorname{Finset}(I), w: I \to \mathbb{R},\\{}q: {\forall i: I, X \to \operatorname{Output}(O, i)},\\{}{\forall i\in J, 0 < \operatorname{Weight}(w, i)} \Rightarrow\\{}{\forall x, y\in X, (\operatorname{WeightedCoordinateDistance}(J, w, q, x, y) = 0) \iff (\operatorname{JointReadout}(J, q, x) = \operatorname{JointReadout}(J, q, y))} \land\\{}{\forall x, y\in X, \operatorname{WeightedObservationQuotientDistance}(J, w, q, \operatorname{QuotientClass}(J, q, x), \operatorname{QuotientClass}(J, q, y)) = \operatorname{WeightedCoordinateDistance}(J, w, q, x, y)} \land\\{}{\forall u, v\in \operatorname{ObservationQuotient}(J, q), 0 \leq \operatorname{WeightedObservationQuotientDistance}(J, w, q, u, v)} \land\\{}{\forall u\in \operatorname{ObservationQuotient}(J, q), \operatorname{WeightedObservationQuotientDistance}(J, w, q, u, u) = 0} \land\\{}{\forall u, v\in \operatorname{ObservationQuotient}(J, q), \operatorname{WeightedObservationQuotientDistance}(J, w, q, u, v) = \operatorname{WeightedObservationQuotientDistance}(J, w, q, v, u)} \land\\{}{\forall u, v, z\in \operatorname{ObservationQuotient}(J, q), \operatorname{WeightedObservationQuotientDistance}(J, w, q, u, z) \leq \operatorname{max}(\operatorname{WeightedObservationQuotientDistance}(J, w, q, u, v), \operatorname{WeightedObservationQuotientDistance}(J, w, q, v, z))} \land\\{}{\forall u, v\in \operatorname{ObservationQuotient}(J, q), (\operatorname{WeightedObservationQuotientDistance}(J, w, q, u, v) = 0) \iff (u = v)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometryLaws/WeightedObservationQuotientUltrametric.weighted_observation_zero_kernel_and_quotient_ultrametric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite budget J selects a dependent family of readouts. The source distance is the largest selected positive weight at which two readout coordinates differ.

The quotient is the kernel quotient of the selected joint readout. The displayed computation rule names the canonical lift of the source distance rather than an unspecified existence witness.

The public clauses give the source zero kernel, the lift computation, nonnegativity, diagonal zero, symmetry, the strong triangle inequality, and identity of indiscernibles on the quotient.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometryLaws/WeightedObservationQuotientUltrametric.weighted_observation_zero_kernel_and_quotient_ultrametric`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../../ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion.md)
- Dependency: [D5/S3/Observer/MetricGeometryLaws/WeightedPredictionZeroKernel](WeightedPredictionZeroKernel.md)
