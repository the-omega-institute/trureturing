# Shifting the regular Gaussian integral

## Abstract

Gaussian integration of a holomorphic function with quadratic strip growth.

**Theorem 1.1 (Real part of the vertical Gaussian exponent).**

Lean statement: `D5/S3/Analytic/Laplace/GaussianBoundaryContour.gaussian_exponent_re`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/GaussianBoundaryContour.gaussian_exponent_re` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real M, c, y, and t, the real part of (c+it)y+(c+it)^2/(2M^2) is cy+(c^2-t^2)/(2M^2). This is the real projection of the expanded Bromwich exponent.

**Theorem 1.2 (Integrable quadratic Gaussian majorant).**

Lean statement: `D5/S3/Analytic/Laplace/GaussianBoundaryContour.gaussian_polynomial_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/GaussianBoundaryContour.gaussian_polynomial_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive b, the function (1+|t|)^2 exp(-b t^2) is integrable on the real line. Gaussian moments of orders zero and two dominate the quadratic factor.

**Theorem 1.3 (Absolute convergence on vertical lines).**

Lean statement: `D5/S3/Analytic/Laplace/GaussianBoundaryContour.regular_vertical_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/GaussianBoundaryContour.regular_vertical_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let J be holomorphic on the open strip from minus one fifth to one and bounded by C times the square of one plus the absolute imaginary part on the closed strip from minus one sixth to three quarters. For every positive M, real y, and real c in that closed strip, the function J(c+it) exp((c+it)y+(c+it)^2/(2M^2)) is absolutely integrable in t. Its norm is bounded by a constant times a quadratic polynomial times exp(-t^2/(2M^2)).

**Theorem 1.4 (A cubic bound after moving the contour).**

Lean statement: `D5/S3/Analytic/Laplace/GaussianBoundaryContour.gaussian_regular_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/GaussianBoundaryContour.gaussian_regular_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same strip assumptions there is a positive constant C such that, for every M at least one and every real y, the normalized Gaussian integral of J on real part three quarters has norm at most C M^3 exp(-y/6). Gaussian decay makes the horizontal cross-sections vanish at both ends of the strip, so the vertical integral equals the integral on real part minus one sixth. Rescaling t by M bounds the remaining quadratic Gaussian moment by a fixed constant times M^3.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/GaussianBoundaryContour.gaussian_exponent_re`
- Truth anchor: `D5/S3/Analytic/Laplace/GaussianBoundaryContour.gaussian_polynomial_integrable`
- Truth anchor: `D5/S3/Analytic/Laplace/GaussianBoundaryContour.gaussian_regular_bound`
- Truth anchor: `D5/S3/Analytic/Laplace/GaussianBoundaryContour.regular_vertical_integrable`
- Dependency: [D5/S3/Analytic/Asymptotics/BarnesResidue](../Asymptotics/BarnesResidue.md)
- Dependency: [D5/S3/Analytic/Fourier/GaussianKernel](../Fourier/GaussianKernel.md)
- Dependency: [D5/S3/Analytic/Laplace/GaussianStripControl](GaussianStripControl.md)
