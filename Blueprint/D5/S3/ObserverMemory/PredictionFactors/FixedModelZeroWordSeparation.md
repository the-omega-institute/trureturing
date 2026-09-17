# Fixed-Model Zero-Word Separation

## Abstract

Two fixed binary models have separated predictions along all long zero words.

The hidden bit is initially fair. It emits a report before flipping with probability one quarter. The probability of a zero report is p from hidden bit zero and one minus p from hidden bit one. The emission parameter stays fixed throughout each history.

**Definition 1.1 (Unnormalized zero-word masses).**

$$\forall p\in \mathbb{R}, v\left(p, 0\right)=(\frac{1}{2}, \frac{1}{2}),\ \forall n\in \mathbb{N}, v\left(p, n + 1\right)=(\frac{3}{4} \cdot p \cdot v\left(p, n\right)_{0} + \frac{1}{4} \cdot \left(1 - p\right) \cdot v\left(p, n\right)_{1}, \frac{1}{4} \cdot p \cdot v\left(p, n\right)_{0} + \frac{3}{4} \cdot \left(1 - p\right) \cdot v\left(p, n\right)_{1})$$

*Formalization.* `D5/S3/ObserverMemory/PredictionFactors/FixedModelZeroWordSeparation.zeroMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two coordinates of v(p,n) are the joint masses of n zero reports and the final hidden bit. Coordinates are numbered zero and one. The recurrence is the column-vector update P diag(p,1-p), with the emission preceding the flip. For the two parameters below both coordinates are positive at every finite length.

**Definition 1.2 (Posterior hidden-bit probability).**

$$\forall p\in \mathbb{R}, n\in \mathbb{N}, Q\left(p, n\right)=\frac{v\left(p, n\right)_{1}}{v\left(p, n\right)_{0} + v\left(p, n\right)_{1}}$$

*Formalization.* `D5/S3/ObserverMemory/PredictionFactors/FixedModelZeroWordSeparation.zeroPosterior` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Q(p,n) denotes zeroPosterior p n. Dividing the hidden-one mass by the total word mass conditions on the finite zero word.

**Definition 1.3 (Current next-zero probability).**

$$\forall p\in \mathbb{R}, n\in \mathbb{N}, A\left(p, n\right)=p + \left(1 - 2 \cdot p\right) \cdot Q\left(p, n\right)$$

*Formalization.* `D5/S3/ObserverMemory/PredictionFactors/FixedModelZeroWordSeparation.zeroPrediction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A(p,n) denotes zeroPrediction p n. The next report is emitted from the current hidden bit; this readout is conditional on the fixed model, without a prior over model indices.

**Theorem 1.4 (Uniform rational separation).**

$$\begin{gathered}(\forall n\in \mathbb{N}, Q\left(\frac{1}{3}, n\right)<\frac{9}{14} \land A\left(\frac{1}{3}, n\right)<\frac{23}{42}) \land\\(\forall i, j\in \mathbb{N}, i<j \Rightarrow Q\left(\frac{1}{4}, i\right)<Q\left(\frac{1}{4}, j\right)) \land\\Q\left(\frac{1}{4}, 3\right)=\frac{19}{28} \land A\left(\frac{1}{4}, 3\right)=\frac{33}{56} \land\\(\forall n\in \mathbb{N}, 3\le n \Rightarrow \frac{A\left(\frac{1}{4}, n\right) - A\left(\frac{1}{3}, n\right)}{2}>\frac{1}{48})\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/PredictionFactors/FixedModelZeroWordSeparation.fixed_model_zero_word_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For emission parameter one third, the positive mass vector remains in the cone 5 v1 < 9 v0. For emission parameter one quarter, the cross determinant of consecutive mass vectors is positive: its first value is positive and each step multiplies it by 3/32. Normalization therefore gives a strictly increasing posterior. Its value at length three and the other model's invariant bound imply separation at every later length. The theorem concerns the common zero-word family and does not assert statistical indistinguishability of the models.

## References

- Truth anchor: `D5/S3/ObserverMemory/PredictionFactors/FixedModelZeroWordSeparation.fixed_model_zero_word_separation`
- Truth anchor: `D5/S3/ObserverMemory/PredictionFactors/FixedModelZeroWordSeparation.zeroMass`
- Truth anchor: `D5/S3/ObserverMemory/PredictionFactors/FixedModelZeroWordSeparation.zeroPosterior`
- Truth anchor: `D5/S3/ObserverMemory/PredictionFactors/FixedModelZeroWordSeparation.zeroPrediction`
