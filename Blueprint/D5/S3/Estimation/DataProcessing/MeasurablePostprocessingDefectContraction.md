# Measurable Postprocessing Defect Contraction

## Abstract

Measurable target postprocessing contracts the source-fiber defect of observable kernel laws.

**Theorem 1.1 (Measurable postprocessing contracts the observable-kernel defect).**

$$\begin{gathered}\forall X, B, C: \operatorname{Type},\\{}\operatorname{MeasurableSpace}\left(X\right), \operatorname{MeasurableSpace}\left(B\right), \operatorname{MeasurableSpace}\left(C\right),\\{}K: \operatorname{Kernel}\left(X, X\right), q: X \to B,\\{}r: B \to C, \operatorname{Measurable}\left(r\right) \Rightarrow\\{}\operatorname{postprocessedObservableKernelDefect}\left(K, q, r\right) \leq \operatorname{observableKernelDefect}\left(K, q\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/MeasurablePostprocessingDefectContraction.measurable_postprocessing_defect_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The event-supremum total-variation distance is constructed directly from measures. Each observable law is the corresponding row of K mapped through q, and the postprocessed law maps that measure through r.

For every measurable event in C, measurability of r identifies its probability after mapping with the probability of the measurable preimage event in B. The associated directed gap is therefore one of the terms in the original event supremum.

The pointwise contraction is applied to every pair of source states with the same q-value and then lifted through the outer supremum. The proof uses pinned Mathlib's kernel and measure map computation rules.

## References

- Truth anchor: `D5/S3/Estimation/DataProcessing/MeasurablePostprocessingDefectContraction.measurable_postprocessing_defect_le`
