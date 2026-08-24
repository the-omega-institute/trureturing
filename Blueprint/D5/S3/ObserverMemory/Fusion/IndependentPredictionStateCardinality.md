# Independent Prediction State Cardinality

## Abstract

Independent predictive components have a product completion and multiplicative finite state count.

**Theorem 1.1 (Independent prediction state cardinality is multiplicative).**

$$\begin{gathered}\forall tau1, tau2, q1, q2,\\{}[\operatorname{Finite} \operatorname{CompletedState}\left(tau1, q1\right)] [\operatorname{Finite} \operatorname{CompletedState}\left(tau2, q2\right)],\\\operatorname{Nonempty}(\operatorname{CompletedState}\left(\operatorname{productUpdate}\left(tau1, tau2\right), \operatorname{productReadout}\left(q1, q2\right)\right) \equiv (\operatorname{CompletedState}\left(tau1, q1\right))\times(\operatorname{CompletedState}\left(tau2, q2\right))) \land\\\operatorname{predictiveStateCount}\left(\operatorname{CompletedState}\left(\operatorname{productUpdate}\left(tau1, tau2\right), \operatorname{productReadout}\left(q1, q2\right)\right)\right) = \operatorname{predictiveStateCount}\left(\operatorname{CompletedState}\left(tau1, q1\right)\right) \times \operatorname{predictiveStateCount}\left(\operatorname{CompletedState}\left(tau2, q2\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Fusion/IndependentPredictionStateCardinality.finite_independent_prediction_state_cardinality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The predictive state count is the finite cardinality of a completed-state carrier. Assume that the completed states of both component systems are finite.

For the componentwise product update and paired product readout, the global completed-state quotient is equivalent to the Cartesian product of the two component quotients. Consequently its predictive state count is the product, rather than the sum, of the two component counts.

The previously established independent-product equivalence supplies the decomposition. Invariance of finite cardinality under equivalence and the cardinality rule for product types then give the multiplication law. The result concerns two components and does not assert a general finite-family decomposition.

## References

- Truth anchor: `D5/S3/ObserverMemory/Fusion/IndependentPredictionStateCardinality.finite_independent_prediction_state_cardinality`
- Dependency: [D5/S3/ObserverMemory/Fusion/IndependentProductCompletion](IndependentProductCompletion.md)
