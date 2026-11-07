# Gaussian boundary formula

## Abstract

Gaussian averages and the boundary of a paired Laplace transform.

**Theorem 1.1 (Cancellation of the Gaussian spectral sum).**

Lean statement: `D5/S3/Analytic/Laplace/GaussianBoundary.gaussian_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/GaussianBoundary.gaussian_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a positive locally finite spectrum have counting function asymptotic to T log(T)/(2 pi). Let f be measurable and bounded on every interval [0,A] with A>=0. Assume its Laplace integral converges absolutely for every Re(s)>1/2, and, on the strip 1/2<Re(s)<1, equals minus one half of the multiplicity-weighted paired pole series plus J. Assume there is 0<eta<1/5 such that J is holomorphic for -eta<Re(s)<1 and has quadratic growth for abs(Re(s))<=eta/2. In addition, assume J is holomorphic for -1/5<Re(s)<1 and has quadratic growth in the imaginary direction on the closed strip from -1/6 to 3/4. There is a positive constant C such that, for M and y at least one, the positive-ray Gaussian average of f is absolutely integrable, and its sum with the Gaussian-weighted cosine spectrum has absolute value at most C M cubed exp(-y/6). Absolute Fubini on Re(s)=3/4 gives Gaussian inversion. Shifting J to Re(s)=-1/6 bounds its contribution. A common quadratic majorant permits passage from finite pole cutoffs to the infinite expansion, while the inverse-square spectral mass bounds the reflected negative-ray corrections.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/GaussianBoundary.gaussian_boundary`
- Dependency: [D5/S3/Analytic/Fourier/GaussianKernel](../Fourier/GaussianKernel.md)
- Dependency: [D5/S3/Analytic/Laplace/GaussianBoundaryContour](GaussianBoundaryContour.md)
- Dependency: [D5/S3/Analytic/Laplace/GaussianBoundaryCorrections](GaussianBoundaryCorrections.md)
- Dependency: [D5/S3/Analytic/Laplace/GaussianBoundaryPoles](GaussianBoundaryPoles.md)
- Dependency: [D5/S3/Analytic/Laplace/GaussianStripControl](GaussianStripControl.md)
- Dependency: [D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity](QuantitativeFejerBoundary/DampedIdentity.md)
- Dependency: [D5/S3/Analytic/Oscillation/GaussianSpectrum](../Oscillation/GaussianSpectrum.md)
