# Prediction Escape as Expansion Escape

## Abstract

Finite-horizon prediction escape is exactly escape from a current readout to its finite-time projection.

**Theorem 1.1 (Bounded prediction escape is finite-time readout expansion escape).**

$$\begin{gathered}\forall X, O: \operatorname{Type},\\{}[\operatorname{DecidableEq}\left(O\right)],\\{}q: X \to O, tau: X \to X,\\{}N: \mathbb{N}, x, y: X,\\{}\operatorname{PredictionEscape}\left(q, tau, N, x, y\right) \iff\\{}\operatorname{ExpansionEscape}\left(q, \operatorname{timeProjection}\left(q, tau, N\right), x, y\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/TimeProjection/PredictionExpansionEscape.prediction_escape_iff_expansion_escape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

PredictionEscape is defined independently by equality of the current readout and a natural-number witness k no later than N where the iterated readouts differ.

ExpansionEscape instead compares equality under the old readout with inequality of the two functions on Fin(N+1). Decidable equality on the output supports a finite scan from function inequality back to a bounded witness.

## References

- Truth anchor: `D5/S3/ConceptDynamics/TimeProjection/PredictionExpansionEscape.prediction_escape_iff_expansion_escape`
