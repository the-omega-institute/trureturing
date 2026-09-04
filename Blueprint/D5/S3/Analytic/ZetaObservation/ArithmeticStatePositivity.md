# Arithmetic State Positivity

## Abstract

The normalized zeta state induces a positive arithmetic seminorm and its Hilbert completion.

**Theorem 1.1 (The arithmetic state is positive and completes to a Hilbert space).**

$$\forall s \in \mathbb{R}, F \in C_{b}(\mathbb{N}, \mathbb{C}),\; 1 < s \Rightarrow \left(0 \le \frac{1}{\Re(\operatorname{riemannZeta}\left(s\right))} \times \sum_{n\in\mathbb{N}} \left\lVert F\left(n\right) \right\rVert^{2} \times n^{-s} \land \left(\operatorname{arithmeticState}\left(s, \overline{F} \times F\right) = \operatorname{ofReal}\left(\frac{1}{\Re(\operatorname{riemannZeta}\left(s\right))} \times \sum_{n\in\mathbb{N}} \left\lVert F\left(n\right) \right\rVert^{2} \times n^{-s}\right) \land \left(\operatorname{ofReal}\left(\left\lVert \operatorname{toArithmeticPreHilbert}\left(s, F\right) \right\rVert^{2}\right) = \operatorname{arithmeticState}\left(s, \overline{F} \times F\right) \land \left(\left(\operatorname{CompletionCoe}\left(\operatorname{toArithmeticPreHilbert}\left(s, F\right)\right) = 0 \Leftrightarrow \left\lVert \operatorname{toArithmeticPreHilbert}\left(s, F\right) \right\rVert = 0\right) \land \left(\operatorname{DenseRange}\left((x: \operatorname{ArithmeticPreHilbert}\left(s\right) \mapsto \operatorname{CompletionCoe}\left(x\right))\right) \land \left(\operatorname{CompleteSpace}\left(\operatorname{ArithmeticHilbertSpace}\left(s\right)\right) \land \left(\forall x \in \operatorname{ArithmeticHilbertSpace}\left(s\right),\; \left\lVert x \right\rVert^{2} = \Re(\operatorname{inner}\left(\mathbb{C}, x, x\right))\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/ArithmeticStatePositivity.arithmetic_positivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A bounded complex observable is integrated against the repository's normalized zeta distribution at a real parameter above one. The zeroth natural-number term has zero mass, so the displayed natural sum is the source sum over positive integers.

The first three conjuncts state positivity, the exact normalized weighted integer expansion, and the induced seminorm-square identity. The normalized series is nonnegative, the full complex state value equals its real coercion, and the real seminorm square equals that complex state value after coercion.

The remaining conjuncts expose the canonical separation and completion: an observable maps to zero exactly when its seminorm vanishes, the canonical range is dense, the completion is complete, and its norm square is its self inner product.

The construction uses the existing zeta distribution together with the pinned library's pre-inner-product core and uniform completion. No conjectural positivity principle is assumed.

## References

- Truth anchor: `D5/S3/Analytic/ZetaObservation/ArithmeticStatePositivity.arithmetic_positivity`
