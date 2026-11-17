# Gaussian integration of paired poles

## Abstract

Absolute Gaussian integration of a paired spectral pole expansion.

**Theorem 1.1 (Absolute integrability of the full series).**

Lean statement: `D5/S3/Analytic/Laplace/GaussianBoundaryPoles.pole_gaussian_tsum_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/GaussianBoundaryPoles.pole_gaussian_tsum_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the weighted ordinate count has the specified logarithmic asymptotic, the full paired-pole series multiplied by the Gaussian factor is integrable on Re(s)=3/4. The sum of m/gamma squared is finite and supplies a single integrable quadratic majorant.

**Theorem 1.2 (Exhaustion by ordinate cutoffs).**

Lean statement: `D5/S3/Analytic/Laplace/GaussianBoundaryPoles.spectrum_cut_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/GaussianBoundaryPoles.spectrum_cut_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

As the real cutoff tends to infinity, the finite set of ordinates below that cutoff tends to the filter of all finite subsets. The cutoffs are increasing and every ordinate belongs to one.

**Theorem 1.3 (Convergence of finite-cutoff integrals).**

Lean statement: `D5/S3/Analytic/Laplace/GaussianBoundaryPoles.pole_gaussian_cutoff_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/GaussianBoundaryPoles.pole_gaussian_cutoff_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integrals of the Gaussian-weighted finite paired-pole sums converge, as the ordinate cutoff tends to infinity, to the integral of the full paired-pole series. Absolute summability of the integrated norms permits passage along the finite cutoffs.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/GaussianBoundaryPoles.pole_gaussian_cutoff_tendsto`
- Truth anchor: `D5/S3/Analytic/Laplace/GaussianBoundaryPoles.pole_gaussian_tsum_integrable`
- Truth anchor: `D5/S3/Analytic/Laplace/GaussianBoundaryPoles.spectrum_cut_tendsto`
- Dependency: [D5/S3/Analytic/Fourier/GaussianKernel](../Fourier/GaussianKernel.md)
- Dependency: [D5/S3/Analytic/Laplace/GaussianBoundaryContour](GaussianBoundaryContour.md)
- Dependency: [D5/S3/Analytic/Laplace/PairedPoleRegularity](PairedPoleRegularity.md)
- Dependency: [D5/S3/Analytic/Oscillation/GaussianSpectrum](../Oscillation/GaussianSpectrum.md)
