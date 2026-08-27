# Completion Kernel Greatest Fixed Point

## Abstract

The completed observation kernel is the greatest forward-invariant kernel relation.

**Theorem 1.1 (The completion kernel is the greatest fixed point).**

$$\begin{gathered}\forall Y: Type, O: Type,\\{}\tau: Y \to Y, q: Y \to O,\\{}\operatorname{ker}(\operatorname{completeItinerary}(\tau, q)) = \operatorname{gfp}(\operatorname{refinementOperator}(\tau, q)) \land\\{}\operatorname{ker}(\operatorname{completeItinerary}(\tau, q)) \subseteq \operatorname{observationKernel}(q) \land\\{}(\forall p: Y \times Y, p \in \operatorname{ker}(\operatorname{completeItinerary}(\tau, q)) \Rightarrow (\tau(\operatorname{fst}(p)), \tau(\operatorname{snd}(p))) \in \operatorname{ker}(\operatorname{completeItinerary}(\tau, q))) \land\\{}\forall R: \operatorname{Set}(Y \times Y), R \subseteq \operatorname{observationKernel}(q) \Rightarrow (\forall p: Y \times Y, p \in R \Rightarrow (\tau(\operatorname{fst}(p)), \tau(\operatorname{snd}(p))) \in R) \Rightarrow R \subseteq \operatorname{ker}(\operatorname{completeItinerary}(\tau, q)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/RefinementClosure/CompletionKernelGreatestFixedPoint.completion_kernel_is_greatest_fixed_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an update tau and readout q, the completed kernel relates states whose canonical complete itineraries agree.

The one-step refinement operator intersects the current observation kernel with the pullback of a candidate relation through tau.

The completed kernel is its greatest fixed point. The public statement also exposes containment in the current kernel, forward invariance, and maximality among every relation with those two properties.

## References

- Truth anchor: `D5/S3/ObserverMemory/RefinementClosure/CompletionKernelGreatestFixedPoint.completion_kernel_is_greatest_fixed_point`
- Dependency: [D5/S3/Observer/Separation/FiniteFutureCongruence](../../Observer/Separation/FiniteFutureCongruence.md)
- Dependency: [D5/S3/ObserverMemory/Prediction/ItineraryCompletion](../Prediction/ItineraryCompletion.md)
