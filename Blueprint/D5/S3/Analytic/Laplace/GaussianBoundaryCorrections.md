# Gaussian half-line corrections

## Abstract

Reflected Gaussian corrections for positive-ray cosine integrals.

**Theorem 1.1 (Cosine inversion on a half-line).**

Lean statement: `D5/S3/Analytic/Laplace/GaussianBoundaryCorrections.gaussian_cos_halfline`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/GaussianBoundaryCorrections.gaussian_cos_halfline` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive Gaussian scale, the integral of cos(gamma u) against q_M(y-u) on the nonnegative half-line equals exp(-gamma squared divided by twice M squared) cos(gamma y), less the integral of cos(gamma v) q_M(y+v) over v at least zero. Split the full Gaussian cosine convolution at zero and reflect the negative half-line.

**Theorem 1.2 (Absolute summability of the corrections).**

Lean statement: `D5/S3/Analytic/Laplace/GaussianBoundaryCorrections.gaussian_corrections_summable`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/GaussianBoundaryCorrections.gaussian_corrections_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the multiplicity count of a locally finite positive spectrum is asymptotic to T log(T) divided by twice pi. For M and y at least one, the reflected Gaussian corrections, multiplied by their spectral multiplicities, form an absolutely summable family. Two integrations by parts bound each term by a common factor times multiplicity divided by gamma squared.

**Theorem 1.3 (An exponentially small correction sum).**

Lean statement: `D5/S3/Analytic/Laplace/GaussianBoundaryCorrections.gaussian_corrections_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/GaussianBoundaryCorrections.gaussian_corrections_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same spectral counting assumption, there is a positive constant C, independent of M and y, such that for M and y at least one the absolute value of the summed multiplicity-weighted reflected corrections is at most C M cubed exp(-y/6). The inverse-square spectral sum is finite, and the Gaussian factor obeys M squared times y times q_M(y) at most three M cubed exp(-y/6) divided by sqrt(2 pi).

**Theorem 1.4 (Summing the positive-ray cosine integrals).**

Lean statement: `D5/S3/Analytic/Laplace/GaussianBoundaryCorrections.gaussian_halfline_summable`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/GaussianBoundaryCorrections.gaussian_halfline_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For M and y at least one, the integrals of the spectral cosines against q_M(y-u) on the nonnegative half-line, with multiplicities included, form a summable family. They are the differences between the summable Gaussian cosine coefficients and the summable reflected corrections.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/GaussianBoundaryCorrections.gaussian_corrections_bound`
- Truth anchor: `D5/S3/Analytic/Laplace/GaussianBoundaryCorrections.gaussian_corrections_summable`
- Truth anchor: `D5/S3/Analytic/Laplace/GaussianBoundaryCorrections.gaussian_cos_halfline`
- Truth anchor: `D5/S3/Analytic/Laplace/GaussianBoundaryCorrections.gaussian_halfline_summable`
- Dependency: [D5/S3/Analytic/Fourier/GaussianKernel](../Fourier/GaussianKernel.md)
- Dependency: [D5/S3/Analytic/Oscillation/GaussianSpectrum](../Oscillation/GaussianSpectrum.md)
