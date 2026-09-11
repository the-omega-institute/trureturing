# Theta integrals on the positive half-line

## Abstract

Theta integrals on the positive half-line.

**Theorem 1.1 (Gaussian integrability under exponential tilts).**

Lean statement: `D5/S3/Analytic/Fourier/ThetaHalfLine.integrable_tilted_gaussian`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/ThetaHalfLine.integrable_tilted_gaussian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dan Romik (2021). *Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases*. URL: <https://doi.org/10.4064/aa200515-10-3>.

*Commentary.*

For every real b, exp(-x^2+b*x) is integrable on the real line, by the complex Gaussian integral API.

**Theorem 1.2 (Absolute convergence from the kernel bound).**

Lean statement: `D5/S3/Analytic/Fourier/ThetaHalfLine.ray_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/ThetaHalfLine.ray_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dan Romik (2021). *Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases*. URL: <https://doi.org/10.4064/aa200515-10-3>.

*Commentary.*

If a continuous real function f satisfies |f(x)| <= sourceThetaKernel(x) for all x >= 0, then f(x)*exp(w*x) is integrable on the positive half-line for every complex w.

**Theorem 1.3 (The endpoint at infinity).**

Lean statement: `D5/S3/Analytic/Fourier/ThetaHalfLine.ray_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/ThetaHalfLine.ray_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dan Romik (2021). *Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases*. URL: <https://doi.org/10.4064/aa200515-10-3>.

*Commentary.*

Under the same pointwise domination, f(x)*exp(w*x) tends to zero as x tends to positive infinity, for every complex w.

**Theorem 1.4 (Convergence for the theta tail).**

Lean statement: `D5/S3/Analytic/Fourier/ThetaHalfLine.psi_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/ThetaHalfLine.psi_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dan Romik (2021). *Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases*. URL: <https://doi.org/10.4064/aa200515-10-3>.

*Commentary.*

For every complex w, psi(x)*exp(w*x) is absolutely integrable on x > 0.

**Theorem 1.5 (Convergence for the first derivative).**

Lean statement: `D5/S3/Analytic/Fourier/ThetaHalfLine.psiFirst_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/ThetaHalfLine.psiFirst_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dan Romik (2021). *Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases*. URL: <https://doi.org/10.4064/aa200515-10-3>.

*Commentary.*

For every complex w, psiFirst(x)*exp(w*x) is absolutely integrable on x > 0.

**Theorem 1.6 (Two integrations by parts).**

Lean statement: `D5/S3/Analytic/Fourier/ThetaHalfLine.kernel_halfline_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/ThetaHalfLine.kernel_halfline_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dan Romik (2021). *Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases*. URL: <https://doi.org/10.4064/aa200515-10-3>.

*Commentary.*

For every complex w, the integral over x > 0 of sourceThetaKernel(x)*exp(w*x) equals 1/4 + w*psi(0) + (w^2-1/4)*thetaLaplace(w). All endpoint limits and the integrability of each derivative term are proved from the actual theta tail.

## References

- Truth anchor: `D5/S3/Analytic/Fourier/ThetaHalfLine.integrable_tilted_gaussian`
- Truth anchor: `D5/S3/Analytic/Fourier/ThetaHalfLine.kernel_halfline_integral`
- Truth anchor: `D5/S3/Analytic/Fourier/ThetaHalfLine.psiFirst_integrable`
- Truth anchor: `D5/S3/Analytic/Fourier/ThetaHalfLine.psi_integrable`
- Truth anchor: `D5/S3/Analytic/Fourier/ThetaHalfLine.ray_integrable`
- Truth anchor: `D5/S3/Analytic/Fourier/ThetaHalfLine.ray_tendsto`
- Dependency: [D5/S3/Analytic/Fourier/ThetaDifferentialKernel](ThetaDifferentialKernel.md)
