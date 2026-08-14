# Convolution-Square Positivity

## Abstract

The Fourier transform of a Weil convolution square is a nonnegative real norm square.

**Theorem 1.1 (Angular frequency matches mathlib Fourier frequency).**

$$\forall g \in \mathcal{W}, \xi \in \mathbb{R}, \operatorname{fourierLaplace}(g, \xi) = \mathcal{F}(g)(\frac{\xi}{2\pi})$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/ConvolutionSquarePositivity.fourierLaplace_real_eq_fourier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Weil test function, the angular-frequency Fourier-Laplace transform at xi equals mathlib's real Fourier transform at xi divided by two pi. The theorem is the normalization bridge between the repository kernel and mathlib's Fourier convention.

**Theorem 1.2 (A convolution square transforms to a norm square).**

$$\forall g \in \mathcal{W}, \xi \in \mathbb{R}, \operatorname{fourierLaplace}(g*\widetilde{g}, \xi) = \lvert\operatorname{fourierLaplace}(g, \xi)\rvert^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/ConvolutionSquarePositivity.fourierLaplace_convolutionSquare_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real-axis transform of g convolved with its Weil involution is the complex norm square of the transform of g. The proof applies mathlib's Fourier convolution theorem and converts the involution transform to complex conjugation.

**Theorem 1.3 (A convolution-square transform is real and nonnegative).**

$$\forall g \in \mathcal{W}, \xi \in \mathbb{R}, \operatorname{Im}(\operatorname{fourierLaplace}(g*\widetilde{g}, \xi)) = 0 \land 0 \leq \Re(\operatorname{fourierLaplace}(g*\widetilde{g}, \xi))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/ConvolutionSquarePositivity.fourierLaplace_convolutionSquare_real_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Because the preceding identity is a real norm square, its imaginary part vanishes and its real part is nonnegative at every real frequency. This is the Fourier-side positivity kernel for convolution-square Weil tests.

## References

- Truth anchor: `D5/S3/Weil/TestFunctions/ConvolutionSquarePositivity.fourierLaplace_convolutionSquare_real`
- Truth anchor: `D5/S3/Weil/TestFunctions/ConvolutionSquarePositivity.fourierLaplace_convolutionSquare_real_nonnegative`
- Truth anchor: `D5/S3/Weil/TestFunctions/ConvolutionSquarePositivity.fourierLaplace_real_eq_fourier`
