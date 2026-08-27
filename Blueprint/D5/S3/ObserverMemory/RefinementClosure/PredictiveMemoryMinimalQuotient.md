# Predictive Memory Minimal Quotient

## Abstract

Every exact predictive memory maps uniquely onto the completed readout-kernel quotient.

**Theorem 1.1 (The predictive quotient is the coarsest exact memory).**

$$\begin{gathered}\forall X, B, M: \operatorname{Type},\\{}F: X \to X, q: X \to B, r: X \to M,\\{}(\exists f: M \to B, q = f \circ r) \land (\exists G: M \to M, r \circ F = G \circ r) \Rightarrow\\{}\exists! theta: \operatorname{range}\left(r\right) \to \operatorname{CompletedState}\left(F, q\right),\\{}\operatorname{completionProjection}\left(F, q\right) = theta \circ \operatorname{rangeFactorization}\left(r\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/RefinementClosure/PredictiveMemoryMinimalQuotient.predictive_memory_minimal_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two public premises are exactly the predictive-memory conditions: the current readout factors through r and r carries a descended update.

The canonical complete itinerary is therefore determined by r. Choosing a representative only inside the realized image of r sends each memory state to its class in the kernel quotient of the complete itinerary.

Representative independence follows from equality of the factored complete itineraries. Surjectivity of the canonical range factorization then proves uniqueness without requiring r to be onto its ambient carrier.

## References

- Truth anchor: `D5/S3/ObserverMemory/RefinementClosure/PredictiveMemoryMinimalQuotient.predictive_memory_minimal_quotient`
- Dependency: [D5/S3/ObserverMemory/PredictionFactors/PredictionCompletionUniversality](../PredictionFactors/PredictionCompletionUniversality.md)
- Dependency: [D5/S3/ObserverMemory/Refinement/PredictionCompletion](../Refinement/PredictionCompletion.md)
