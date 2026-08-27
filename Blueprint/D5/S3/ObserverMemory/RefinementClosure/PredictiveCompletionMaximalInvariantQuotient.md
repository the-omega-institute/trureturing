# Predictive Completion as a Maximal Invariant Quotient

## Abstract

The maximal invariant future kernel carries the canonical predictive quotient.

**Theorem 1.1 (The complete-future kernel yields the coarsest predictive refinement).**

$$\begin{gathered}\forall Y, O: \operatorname{Type},\\{}tau: Y \to Y, q: Y \to O,\\{}\operatorname{let} Kinf := \operatorname{ker}\left(\operatorname{completeItinerary}\left(tau, q\right)\right),\\{}piInf := \operatorname{completionProjection}\left(tau, q\right),\\{}Kpi := \operatorname{ker}\left(piInf\right)\\{}\operatorname{in} [Kpi = Kinf \land\\{}Kinf = \operatorname{gfp}\left(\operatorname{refinementOperator}\left(tau, q\right)\right) \land\\{}Kinf \subseteq \operatorname{observationKernel}\left(q\right) \land\\{}(\forall p: Y \times Y, p \in Kinf \Rightarrow (tau\left(\operatorname{fst}\left(p\right)\right), tau\left(\operatorname{snd}\left(p\right)\right)) \in Kinf) \land\\{}(\forall R: \operatorname{Set}\left(Y \times Y\right), R \subseteq \operatorname{observationKernel}\left(q\right) \Rightarrow (\forall p: Y \times Y, p \in R \Rightarrow (tau\left(\operatorname{fst}\left(p\right)\right), tau\left(\operatorname{snd}\left(p\right)\right)) \in R) \Rightarrow R \subseteq Kinf) \land\\{}(\exists! readoutBar: \operatorname{CompletedState}\left(tau, q\right) \to O, q = readoutBar \circ piInf) \land\\{}\exists! updateBar: \operatorname{CompletedState}\left(tau, q\right) \to \operatorname{CompletedState}\left(tau, q\right), piInf \circ tau = updateBar \circ piInf].\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/RefinementClosure/PredictiveCompletionMaximalInvariantQuotient.predictive_completion_maximal_invariant_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The completed kernel is the equality kernel of the canonical complete itinerary. The projection is the canonical map to its kernel quotient, and the statement explicitly identifies the projection kernel with the completed kernel.

The completed kernel is the greatest fixed point of one-step refinement. It lies inside the current readout kernel, is forward invariant, and contains every relation satisfying those two conditions.

The quotient itself is public: both the current readout and source update descend uniquely through its surjective canonical projection. The proof applies the frozen greatest-fixed-point theorem and pinned quotient exactness and surjectivity rules.

## References

- Truth anchor: `D5/S3/ObserverMemory/RefinementClosure/PredictiveCompletionMaximalInvariantQuotient.predictive_completion_maximal_invariant_quotient`
- Dependency: [D5/S3/ObserverMemory/Refinement/PredictionCompletion](../Refinement/PredictionCompletion.md)
- Dependency: [D5/S3/ObserverMemory/RefinementClosure/CompletionKernelGreatestFixedPoint](CompletionKernelGreatestFixedPoint.md)
