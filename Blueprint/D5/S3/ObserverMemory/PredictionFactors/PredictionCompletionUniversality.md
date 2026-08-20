# Prediction Completion Universality

## Abstract

Compatible coarse dynamics determine the complete future readout.

**Theorem 1.1 (Compatible coarse dynamics complete the future trace).**

$$\begin{gathered}\forall X, B, C,\\F: X \to X, q: X \to B,\\r: X \to C, G: C \to C, h: C \to B,\\(r \circ F = G \circ r \land q = h \circ r) \Rightarrow\\\exists Phi: C \to \left(\mathbb{N} \to B\right), \operatorname{Tr}\left(q, F\right) = Phi \circ r.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/PredictionFactors/PredictionCompletionUniversality.prediction_completion_universality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F update source states, let q read them out, and let r map source states to coarse states. Suppose r intertwines F with a coarse update G and q factors through a coarse readout h.

Define the completed coarse readout at time n by applying h after the n-fold iterate of G. The iterate-semiconjugacy law then identifies this value with the source readout after the n-fold iterate of F.

The Lean theorem uses the existing complete-itinerary primitive. Pinned Mathlib supplies Function.semiconj_iff_comp_eq and the exact iterate transport theorem Function.Semiconj.iterate_right; both are applied directly.

## References

- Truth anchor: `D5/S3/ObserverMemory/PredictionFactors/PredictionCompletionUniversality.prediction_completion_universality`
- Dependency: [D5/S3/ObserverMemory/Prediction/ItineraryCompletion](../Prediction/ItineraryCompletion.md)
