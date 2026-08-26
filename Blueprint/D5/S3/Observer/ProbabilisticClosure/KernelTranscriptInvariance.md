# Statistical Kernel Transcript Invariance

## Abstract

Equal kernel laws give equal randomized transcript laws.

**Theorem 1.1 (Equal kernel laws generate equal transcript laws).**

$$\begin{gathered}\forall X, O, R, D: \operatorname{Type},\\{}[\operatorname{MeasurableSpace}(X)], [\operatorname{MeasurableSpace}(O)], [\operatorname{MeasurableSpace}(R)], [\operatorname{MeasurableSpace}(D)],\\{}K: \operatorname{Kernel}\left(X, O\right), \operatorname{Markov}\left(K\right),\\{}x, y: X, K(x) = K(y) \Rightarrow\\{}\forall n\in \mathbb{N}, P: \operatorname{Kernel}\left(\operatorname{Fin}\left(n\right) \to O, R\right), \operatorname{Markov}\left(P\right),\\{}A: \operatorname{Kernel}\left(R, D\right), \operatorname{Markov}\left(A\right),\\{}\operatorname{bind}\left(\operatorname{bind}\left(\operatorname{ProductMeasure}\left(\operatorname{Fin}\left(n\right), K(x)\right), P\right), A\right) = \operatorname{bind}\left(\operatorname{bind}\left(\operatorname{ProductMeasure}\left(\operatorname{Fin}\left(n\right), K(y)\right), P\right), A\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/KernelTranscriptInvariance.statistical_kernel_transcript_law_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hypothesis is equality of the two probability measures returned by the same Markov channel at x and y. For each public sample count n, the input transcript law is the canonical finite product of that channel measure, including the zero-sample product.

The public kernels P and A respectively model arbitrary Markov postprocessing and a randomized decision rule. Composing both with the finite product laws constructs the final transcript laws rather than defining a transcript to have the desired equality.

Measure equality is preserved first by the finite product constructor and then by both measure-kernel compositions, which yields the displayed equality for every sample count and both processors.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/KernelTranscriptInvariance.statistical_kernel_transcript_law_invariant`
