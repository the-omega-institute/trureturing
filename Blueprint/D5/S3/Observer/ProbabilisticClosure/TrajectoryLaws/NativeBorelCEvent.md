# Started trajectories and stationarity

## Abstract

The original summable-excess event

startedC(F,Q) is the Ionescu-Tulcea kernel for the original C=BA with its initial descriptor fixed to Q. originalTrajectory(F) is its mixture against the original stationary margin nuP. shift(x)(n)=x(n+1). excessSeries(x) is the extended nonnegative sum of ofReal(excess(x(n))); summableExcess is the measurable event excessSeries<infinity. eventProbability(F,Q)=startedC(F,Q)(summableExcess). Every series uses the actual successive states of this C law.

**Theorem 1.1 (Prefix marginals determine a complete sequence measure).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCEvent.measure_eq_of_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCEvent.measure_eq_of_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any measurable alphabet S and measures mu and nu on natural sequences, assume nu is finite and every prefix of length n+1 has the same pushforward measure under mu and nu. Then mu equals nu on the entire product sigma-algebra. Every finite coordinate set lies in one prefix; Mathlib IsProjectiveLimit.unique applies to the finite-coordinate marginals of nu. This determines the native started trajectory laws and the complete conditional future and past measures of OriginalFutureScreening.

**Theorem 1.2 (common flow event harmonic).**

$$\forall F: CommonFlow, \operatorname{map}\left(\operatorname{originalTrajectory}\left(F\right), \operatorname{shift}\left(\right)\right)=\operatorname{originalTrajectory}\left(F\right)\land \operatorname{preimage}\left(\operatorname{shift}\left(\right), \operatorname{summableExcess}\left(\right)\right)=\operatorname{summableExcess}\left(\right)\land \forall Q: PDescriptor, \operatorname{lintegral}\left(\operatorname{CRow}\left(F, Q\right), R, \operatorname{eventProbability}\left(F, R\right)\right)=\operatorname{eventProbability}\left(F, Q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCEvent.common_flow_event_harmonic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite C products commute with deletion of their first coordinate. Uniqueness of the full law from its finite marginals gives the actual started-row shift identity and then stationarity of the original path law. Removing one finite term preserves the finite-series event. Evaluating this identity at that event proves harmonicity of its actual probability for every starting descriptor.

**Theorem 1.3 (common flow event localization).**

$$\forall F: CommonFlow, \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, \operatorname{ofReal}\left(\operatorname{excess}\left(Q\right)\right) \cdot \operatorname{eventProbability}\left(F, Q\right)=0\land (\operatorname{eventProbability}\left(F, Q\right)\neq 0)\Rightarrow(\operatorname{excess}\left(Q\right)=0)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCEvent.common_flow_event_localization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bounded measurable reciprocal (1+excessSeries)^(-1) increases under shift and has the same integral by stationarity. It therefore agrees almost everywhere with its shifted value. On the finite-series event, finite cancellation forces the initial excess to vanish. Disintegrating against the actual started rows gives ofReal(excess(Q))*eventProbability(F,Q)=0. The earned nonnegative excess on the original margin then gives the real zero-excess implication, including the case of event probability zero.

**Theorem 1.4 (common flow event edges).**

$$\forall F: CommonFlow, \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, \operatorname{AE}\left(\operatorname{CRow}\left(F, Q\right), R, \operatorname{eventProbability}\left(F, R\right)=\operatorname{eventProbability}\left(F, Q\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCEvent.common_flow_event_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The harmonic event probability lies in [0,1]. The stationary second moment and the conditional square inequality force zero conditional variance. Thus the probability has the same value at both states of almost every original C edge. This statement concerns the actual event probability.

$\forall F: CommonFlow, \operatorname{AE}\left(\operatorname{originalTrajectory}\left(F\right), x, \forall n: Nat, 0\leq\operatorname{excess}\left(\operatorname{at}\left(x, n\right)\right)\land (\operatorname{member}\left(x, \operatorname{summableExcess}\left(\right)\right))\Leftrightarrow(\operatorname{Summable}\left(n, \operatorname{excess}\left(\operatorname{at}\left(x, n\right)\right)\right))\right)\land \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, \operatorname{AE}\left(\operatorname{startedCRow}\left(F, Q\right), x, \forall n: Nat, 0\leq\operatorname{excess}\left(\operatorname{at}\left(x, n\right)\right)\land (\operatorname{member}\left(x, \operatorname{summableExcess}\left(\right)\right))\Leftrightarrow(\operatorname{Summable}\left(n, \operatorname{excess}\left(\operatorname{at}\left(x, n\right)\right)\right))\right)\right)$Every time marginal of the same original path law is nuP. The source excess bound therefore holds simultaneously at all countably many times. On this carrier the nonnegative extended series is finite exactly when the original real excess series is summable. The same assertion holds in almost every started row after disintegration against nuP.

**Theorem 1.5 (common flow event conditional).**

$$\forall F: CommonFlow, \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, \operatorname{conditionalRow}\left(\operatorname{originalTrajectory}\left(F\right), \operatorname{identity}\left(\right), \operatorname{evalZero}\left(\right), Q\right)=\operatorname{startedCRow}\left(F, Q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCEvent.common_flow_event_conditional` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

conditionalRow(P,identity,evalZero,Q) is the regular conditional distribution of the entire path given its time-zero descriptor. Each started row has that descriptor as its initial state. This proves the full joint identity and identifies the exhibited started kernel with the conditional law almost everywhere. Standard-Borel structure is used for this actual conditional distribution.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCEvent.common_flow_event_conditional`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCEvent.common_flow_event_edges`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCEvent.common_flow_event_harmonic`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCEvent.common_flow_event_localization`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCEvent.measure_eq_of_prefix`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteProducts](NativeBorelFiniteProducts.md)
