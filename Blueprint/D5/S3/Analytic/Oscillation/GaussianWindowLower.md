# Gaussian window lower bounds

## Abstract

Gaussian spectral sums inherit logarithmic window mass from hard cutoffs.

**Theorem 1.1 (Transferring spectral window mass).**

Lean statement: `D5/S3/Analytic/Oscillation/GaussianWindowLower.gaussian_window_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/GaussianWindowLower.gaussian_window_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a positive locally finite spectrum with positive integer multiplicities. Assume N(T)/(T log T) tends to 1/(2 pi), the multiplicity in each unit interval is bounded by a constant times log(T+3), and the averaged Montgomery lower bound holds. There is c>0 such that, for every sufficiently large M, the integral of the squared Gaussian cosine sum over [16 log M-1,20 log M+1] is at least c M (log M)². A smooth cutoff of width M^(1/4) cancels the Gaussian weights below M. Absolute convergence permits convolution term by term. The transition band contributes at most a constant times M^(1/4) log(2+M). Truncating the Gaussian sum to the enlarged interval adds at most a constant times log(2+M) on the inner interval, because the cutoff kernel has integral tail of order 1/M. The combined squared error is negligible compared with M (log M)². The Fourier multiplier bound exp(2) then transfers the hard-cutoff lower bound to the Gaussian sum.

## References

- Truth anchor: `D5/S3/Analytic/Oscillation/GaussianWindowLower.gaussian_window_lower`
- Dependency: [D5/S3/Analytic/Fourier/ConvolutionL2](../Fourier/ConvolutionL2.md)
- Dependency: [D5/S3/Analytic/Fourier/GaussianCutoff](../Fourier/GaussianCutoff.md)
- Dependency: [D5/S3/Analytic/Oscillation/GaussianSpectrum](GaussianSpectrum.md)
- Dependency: [D5/S3/Analytic/Oscillation/MontgomeryWindow](MontgomeryWindow.md)
