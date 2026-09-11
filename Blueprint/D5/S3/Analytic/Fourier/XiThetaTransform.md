# The theta transform and completed zeta

## Abstract

The theta transform and completed zeta.

**Theorem 1.1 (Gaussian integrability under exponential tilts).**

Lean statement: `D5/S3/Analytic/Fourier/XiThetaTransform.integrable_tilted_gaussian`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/XiThetaTransform.integrable_tilted_gaussian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dan Romik (2021). *Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases*. URL: <https://doi.org/10.4064/aa200515-10-3>.

*Commentary.*

For every real b, exp(-x^2+b*x) is integrable on the real line, by the complex Gaussian integral API.

**Theorem 1.2 (Absolute convergence from the kernel bound).**

Lean statement: `D5/S3/Analytic/Fourier/XiThetaTransform.ray_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/XiThetaTransform.ray_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dan Romik (2021). *Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases*. URL: <https://doi.org/10.4064/aa200515-10-3>.

*Commentary.*

If a continuous real function f satisfies |f(x)| <= sourceThetaKernel(x) for all x >= 0, then f(x)*exp(w*x) is integrable on the positive half-line for every complex w.

**Theorem 1.3 (The endpoint at infinity).**

Lean statement: `D5/S3/Analytic/Fourier/XiThetaTransform.ray_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/XiThetaTransform.ray_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dan Romik (2021). *Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases*. URL: <https://doi.org/10.4064/aa200515-10-3>.

*Commentary.*

Under the same pointwise domination, f(x)*exp(w*x) tends to zero as x tends to positive infinity, for every complex w.

**Theorem 1.4 (Convergence for the theta tail).**

Lean statement: `D5/S3/Analytic/Fourier/XiThetaTransform.psi_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/XiThetaTransform.psi_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dan Romik (2021). *Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases*. URL: <https://doi.org/10.4064/aa200515-10-3>.

*Commentary.*

For every complex w, psi(x)*exp(w*x) is absolutely integrable on x > 0.

**Theorem 1.5 (Convergence for the first derivative).**

Lean statement: `D5/S3/Analytic/Fourier/XiThetaTransform.psiFirst_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/XiThetaTransform.psiFirst_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dan Romik (2021). *Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases*. URL: <https://doi.org/10.4064/aa200515-10-3>.

*Commentary.*

For every complex w, psiFirst(x)*exp(w*x) is absolutely integrable on x > 0.

**Theorem 1.6 (Two integrations by parts).**

Lean statement: `D5/S3/Analytic/Fourier/XiThetaTransform.kernel_halfline_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/XiThetaTransform.kernel_halfline_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dan Romik (2021). *Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases*. URL: <https://doi.org/10.4064/aa200515-10-3>.

*Commentary.*

For every complex w, the integral over x > 0 of sourceThetaKernel(x)*exp(w*x) equals 1/4 + w*psi(0) + (w^2-1/4)*thetaLaplace(w). All endpoint limits and the integrability of each derivative term are proved from the actual theta tail.

**Theorem 1.7 (The symmetric Mellin integral).**

Lean statement: `D5/S3/Analytic/Fourier/XiThetaTransform.thetaMellin_eq_completed`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/XiThetaTransform.thetaMellin_eq_completed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dan Romik (2021). *Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases*. URL: <https://doi.org/10.4064/aa200515-10-3>.

*Commentary.*

For every complex s, the literal symmetric theta-tail Mellin integral thetaMellin(s) equals completedRiemannZeta-zero(s). Additive cancellation of the two explicit pole terms in the public reconstruction proves this at s=0 and s=1 as well.

**Theorem 1.8 (All-complex Fourier integrability).**

Lean statement: `D5/S3/Analytic/Fourier/XiThetaTransform.source_theta_fourier_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/XiThetaTransform.source_theta_fourier_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dan Romik (2021). *Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases*. URL: <https://doi.org/10.4064/aa200515-10-3>.

*Commentary.*

For every complex z, sourceThetaKernel(x)*exp(i*z*x) is absolutely integrable on the real line. The Gaussian bound absorbs every complex exponential tilt.

**Theorem 1.9 (The logarithmic substitution).**

Lean statement: `D5/S3/Analytic/Fourier/XiThetaTransform.thetaMellin_center`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/XiThetaTransform.thetaMellin_center` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dan Romik (2021). *Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases*. URL: <https://doi.org/10.4064/aa200515-10-3>.

*Commentary.*

For every complex w, thetaMellin(1/2+w)=2*(thetaLaplace(w)+thetaLaplace(-w)). The proof uses t=exp(2*x) with the exact factor two and justifies splitting the two convergent half-line integrals.

**Theorem 1.10 (The all-complex transform to xi).**

Lean statement: `D5/S3/Analytic/Fourier/XiThetaTransform.source_theta_fourier_eq_xi`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/XiThetaTransform.source_theta_fourier_eq_xi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dan Romik (2021). *Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases*. URL: <https://doi.org/10.4064/aa200515-10-3>.

*Commentary.*

For every complex z, the integral over the real line of sourceThetaKernel(x)*exp(i*z*x) equals xiReading(1/2+i*z). Two integrations by parts on the positive half-line, reflection, and the symmetric Mellin identity prove the result. No division by s*(s-1) occurs, so z=0 and z=plus or minus i/2 are included.

**Theorem 1.11 (The constant coefficient is one).**

Lean statement: `D5/S3/Analytic/Fourier/XiThetaTransform.source_theta_coefficient_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/XiThetaTransform.source_theta_coefficient_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dan Romik (2021). *Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases*. URL: <https://doi.org/10.4064/aa200515-10-3>.

*Commentary.*

The literal normalized theta coefficient sourceThetaCoefficient 0 equals one. The all-complex Fourier identity at zero identifies the total mass with the real xi value at the center, and positivity of the actual kernel proves this denominator is nonzero.

**Theorem 1.12 (Unconditional normalization and positivity).**

Lean statement: `D5/S3/Analytic/Fourier/XiThetaTransform.source_theta_normalized`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/XiThetaTransform.source_theta_normalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dan Romik (2021). *Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases*. URL: <https://doi.org/10.4064/aa200515-10-3>.

*Commentary.*

The real xi value at 1/2 is the integral of sourceThetaKernel and is strictly positive; sourceThetaDensity has integral one; every sourceThetaCoefficient k is strictly positive. The existing normalization theorem is applied with its constant-coefficient premise now proved.

## References

- Truth anchor: `D5/S3/Analytic/Fourier/XiThetaTransform.integrable_tilted_gaussian`
- Truth anchor: `D5/S3/Analytic/Fourier/XiThetaTransform.kernel_halfline_integral`
- Truth anchor: `D5/S3/Analytic/Fourier/XiThetaTransform.psiFirst_integrable`
- Truth anchor: `D5/S3/Analytic/Fourier/XiThetaTransform.psi_integrable`
- Truth anchor: `D5/S3/Analytic/Fourier/XiThetaTransform.ray_integrable`
- Truth anchor: `D5/S3/Analytic/Fourier/XiThetaTransform.ray_tendsto`
- Truth anchor: `D5/S3/Analytic/Fourier/XiThetaTransform.source_theta_coefficient_zero`
- Truth anchor: `D5/S3/Analytic/Fourier/XiThetaTransform.source_theta_fourier_eq_xi`
- Truth anchor: `D5/S3/Analytic/Fourier/XiThetaTransform.source_theta_fourier_integrable`
- Truth anchor: `D5/S3/Analytic/Fourier/XiThetaTransform.source_theta_normalized`
- Truth anchor: `D5/S3/Analytic/Fourier/XiThetaTransform.thetaMellin_center`
- Truth anchor: `D5/S3/Analytic/Fourier/XiThetaTransform.thetaMellin_eq_completed`
- Dependency: [D5/S3/Analytic/CompletedZetaMellinReconstruction](../CompletedZetaMellinReconstruction.md)
- Dependency: [D5/S3/Analytic/Fourier/ThetaDifferentialKernel](ThetaDifferentialKernel.md)
