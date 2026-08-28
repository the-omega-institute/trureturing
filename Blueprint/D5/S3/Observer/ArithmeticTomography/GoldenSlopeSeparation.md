# Golden Slope Separation

## Abstract

The minimum golden-slope gap in a finite positive integer window has a reciprocal linear lower bound.

**Definition 1.1 (Finite-window golden gap set).**

$$\forall H: \mathbb{N}, \operatorname{goldenWindowGapSet}\left(H\right) = \{d \in \mathbb{R} \mid \exists m, n, mPrime, nPrime \in \operatorname{Icc}\left(1, H\right), (m, n) \neq (mPrime, nPrime) \land d = \left|\varphi m + n - (\varphi mPrime + nPrime)\right|\}.$$

*Formalization.* `D5/S3/Observer/ArithmeticTomography/GoldenSlopeSeparation.goldenWindowGapSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The gap set contains exactly the absolute differences between the golden-slope readings of two distinct points in the positive H by H integer window.

**Definition 1.2 (Canonical golden separation).**

$$\forall H: \mathbb{N}, \operatorname{goldenSeparation}\left(H\right) = \operatorname{sInf}\left(\operatorname{goldenWindowGapSet}\left(H\right)\right).$$

*Formalization.* `D5/S3/Observer/ArithmeticTomography/GoldenSlopeSeparation.goldenSeparation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Golden separation is the real infimum of the finite-window gap set. For H at least two that set is nonempty, so this is its minimum pairwise spectral spacing.

**Theorem 1.3 (Golden separation has a reciprocal linear lower bound).**

$$\forall H: \mathbb{N}, 2 \leq H \Rightarrow \frac{1}{\varphi(H - 1)} \leq \operatorname{goldenSeparation}\left(H\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/GoldenSlopeSeparation.golden_separation_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product of a nonzero golden reading difference and its conjugate is a nonzero integer, hence has absolute value at least one. The conjugate factor is at most goldenRatio times H minus one, which gives the bound for every gap and therefore for their infimum.

## References

- Truth anchor: `D5/S3/Observer/ArithmeticTomography/GoldenSlopeSeparation.goldenSeparation`
- Truth anchor: `D5/S3/Observer/ArithmeticTomography/GoldenSlopeSeparation.goldenWindowGapSet`
- Truth anchor: `D5/S3/Observer/ArithmeticTomography/GoldenSlopeSeparation.golden_separation_bound`
- Dependency: [D5/S3/Observer/ArithmeticTomography/IrrationalSlopeFaithfulness](IrrationalSlopeFaithfulness.md)
