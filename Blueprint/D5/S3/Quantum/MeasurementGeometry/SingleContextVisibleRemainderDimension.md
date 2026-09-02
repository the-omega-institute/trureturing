# Single-Context Visible and Remainder Dimensions

## Abstract

One rank-one projective context exposes one diagonal slice of the trace-zero Hermitian state directions and leaves its orthogonal remainder.

**Theorem 1.1 (A single context exposes exactly its diagonal share).**

$$\begin{gathered}\forall d, B: \operatorname{RankOneContext}\left(d\right), d \geq 2 \land \operatorname{IsRecordMeasurement}\left(\operatorname{projector}\left(B\right)\right) \Rightarrow \\{}\operatorname{finrankR}\left(\operatorname{diagonalTraceZeroSubspace}\left(B\right)\right) \le d - 1 \land\\{}\operatorname{finrankR}\left(\operatorname{orthogonal}\left(\operatorname{diagonalTraceZeroSubspace}\left(B\right)\right)\right) = d^{2} - d \land\\{}\operatorname{visibleRatio}\left(B\right) = \frac{d - 1}{d^{2} - 1} \land\\{}\operatorname{visibleRatio}\left(B\right) = \frac{1}{d + 1} \land\\{}\operatorname{remainderRatio}\left(B\right) = \frac{d^{2} - d}{d^{2} - 1} \land\\{}\operatorname{remainderRatio}\left(B\right) = \frac{d}{d + 1} \land\\{}\operatorname{probabilityVectorExposedRatio}\left(B\right) = \frac{1}{d + 1}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/MeasurementGeometry/SingleContextVisibleRemainderDimension.single_context_visible_remainder_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let d be at least two and let B be a complete rank-one projective measurement. Its visible carrier is the repository's canonical diagonalTraceZeroSubspace inside traceZeroHermitian d; the unread carrier is its real Hilbert--Schmidt orthogonal complement.

The visible finrank is at most d minus one, while the orthogonal remainder finrank is d squared minus d. Dividing each by the canonical trace-zero Hermitian finrank gives both displayed forms of the visible and remainder ratios.

The last clause uses the range of contextProbabilityDirection, the actual real-linear probability-vector readout on trace-zero state directions. Its ratio is one over d plus one. This is a ratio of linear dimensions, not probability mass of an individual state.

## References

- Truth anchor: `D5/S3/Quantum/MeasurementGeometry/SingleContextVisibleRemainderDimension.single_context_visible_remainder_dimension`
- Dependency: [D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition](../Entanglement/BipartiteSectorDecomposition.md)
- Dependency: [D5/S3/Quantum/Tomography/OneStepProbabilityInnovation](../Tomography/OneStepProbabilityInnovation.md)
