# Convolution Power Amplification

## Abstract

Repeated convolution turns a strictly separated side packet into a negligible term.

**Theorem 1.1 (The normalized double-centered packet tends to one).**

$$\lim_{n\to\infty} \frac{B_{n+1}(t+i\,delta)}{q_{0}^{n+1}} = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ConvolutionPowerAmplification.double_centered_convolution_power_amplification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The iteration indexed by n contains exactly n+1 convolution factors. Its Fourier-Laplace transform is the corresponding n+1 power, without introducing a zero-fold compactly supported identity.

The cosine-modulated inverse packet has transform B_(n+1), remains smooth and even, and has support in (-(n+1), n+1) when the source test has support in (-1, 1). Real-valuedness is also preserved.

At t+i delta, the main summand is q0^(n+1). The strict norm bound on the other shifted transform makes its ratio to q0 have norm below one, so the normalized side power tends to zero.

## References

- Truth anchor: `D5/S3/Fourier/ConvolutionPowerAmplification.double_centered_convolution_power_amplification`
