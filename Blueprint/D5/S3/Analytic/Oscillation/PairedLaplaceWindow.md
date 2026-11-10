# Gaussian transfer to the original function

## Abstract

Square mass of paired Laplace data on logarithmic windows.

**Theorem 1.1 (A window mean-square lower bound).**

Lean statement: `D5/S3/Analytic/Oscillation/PairedLaplaceWindow.paired_laplace_window_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/PairedLaplaceWindow.paired_laplace_window_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a positive ordinate spectrum have the counting asymptotic N(T)/(T log T) tending to 1/(2 pi), a logarithmic local count, and the averaged Montgomery lower bound. Suppose f has paired Laplace data with quadratic growth, and its regular part is holomorphic and polynomially bounded on the wider Gaussian strip. There is c>0 such that, for all sufficiently large M, the integral of f(y) squared from 16 log M minus two to 20 log M plus two is at least c M (log M) squared. The Gaussian boundary formula compares the Gaussian average with the cosine spectrum. Initial Laplace convergence at three quarters bounds the discarded Gaussian tails after truncating f to the larger window. Young's inequality transfers the remaining square mass to f.

## References

- Truth anchor: `D5/S3/Analytic/Oscillation/PairedLaplaceWindow.paired_laplace_window_lower`
- Dependency: [D5/S3/Analytic/Fourier/ConvolutionL2](../Fourier/ConvolutionL2.md)
- Dependency: [D5/S3/Analytic/Laplace/GaussianBoundary](../Laplace/GaussianBoundary.md)
- Dependency: [D5/S3/Analytic/Oscillation/GaussianWindowLower](GaussianWindowLower.md)
