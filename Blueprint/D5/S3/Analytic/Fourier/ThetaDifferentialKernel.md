# The original theta differential kernel

## Abstract

The original theta differential kernel.

**Theorem 1.1 (Local summable derivative majorants).**

Lean statement: `D5/S3/Analytic/Fourier/ThetaDifferentialKernel.thetaSeries_local_majorant`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/ThetaDifferentialKernel.thetaSeries_local_majorant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dan Romik (2021). *Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases*. URL: <https://doi.org/10.4064/aa200515-10-3>.

*Commentary.*

For every natural k and every a > 0, pi times the weighted Gaussian series of degree k+2 at a is summable and bounds the absolute derivative terms at every t >= a.

**Theorem 1.2 (Differentiating the actual series).**

Lean statement: `D5/S3/Analytic/Fourier/ThetaDifferentialKernel.hasDerivAt_thetaSeries`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/ThetaDifferentialKernel.hasDerivAt_thetaSeries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dan Romik (2021). *Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases*. URL: <https://doi.org/10.4064/aa200515-10-3>.

*Commentary.*

For every k and t > 0, thetaSeries k has derivative -pi times thetaSeries (k+2). The open ray above t/2 supplies the summable majorant required by the series differentiation theorem.

**Theorem 1.3 (The actual theta tail).**

Lean statement: `D5/S3/Analytic/Fourier/ThetaDifferentialKernel.thetaSeries_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/ThetaDifferentialKernel.thetaSeries_zero` (`✓ std3`). ∎

*Citation.* Dan Romik (2021). *Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases*. URL: <https://doi.org/10.4064/aa200515-10-3>.

*Commentary.*

Romik (1.6) states the positive-index theta-tail identity for t > 0. Here thetaSeries 0 t equals (theta t - 1)/2; the Lean proof identifies theta with the even Hurwitz kernel at parameter zero.

**Theorem 1.4 (The original differential weight).**

Lean statement: `D5/S3/Analytic/Fourier/ThetaDifferentialKernel.omega_eq_series`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/ThetaDifferentialKernel.omega_eq_series` (`✓ std3`). ∎

*Citation.* Dan Romik (2021). *Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases*. URL: <https://doi.org/10.4064/aa200515-10-3>.

*Commentary.*

Romik (1.7) gives the positive-integer Gaussian series for omega at t > 0. Separating its two summable weights gives omega(t) = 2*pi^2*t^2*thetaSeries 4 t - 3*pi*t*thetaSeries 2 t; the repository proves this regrouping.

**Theorem 1.5 (The theta differential identity).**

Lean statement: `D5/S3/Analytic/Fourier/ThetaDifferentialKernel.romikPhi_eq_differential`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/ThetaDifferentialKernel.romikPhi_eq_differential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dan Romik (2021). *Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases*. URL: <https://doi.org/10.4064/aa200515-10-3>.

*Commentary.*

For every real x, romikPhi x = deriv (deriv psi) x - psi x / 4. Here psi(x)=exp(x/2)*(theta(exp(2*x))-1)/2 and romikPhi(x)=2*exp(x/2)*omega(exp(2*x)). Both differentiations have explicit locally summable bounds.

**Theorem 1.6 (The modular boundary derivative).**

Lean statement: `D5/S3/Analytic/Fourier/ThetaDifferentialKernel.psi_deriv_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/ThetaDifferentialKernel.psi_deriv_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dan Romik (2021). *Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases*. URL: <https://doi.org/10.4064/aa200515-10-3>.

*Commentary.*

The derivative of psi at zero is -1/4. Differentiating its modular reflection identity establishes this value without a mass-normalization assumption.

**Theorem 1.7 (Evenness from modular differentiation).**

Lean statement: `D5/S3/Analytic/Fourier/ThetaDifferentialKernel.romikPhi_even`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/ThetaDifferentialKernel.romikPhi_even` (`✓ std3`). ∎

*Citation.* Dan Romik (2021). *Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases*. URL: <https://doi.org/10.4064/aa200515-10-3>.

*Commentary.*

Romik (1.9) states Phi(-x)=Phi(x) for every real x, with Phi defined without an absolute value in (1.8). The repository proof differentiates modular reflection: the defects in psi and its second derivative cancel.

**Theorem 1.8 (Identification on the whole real axis).**

Lean statement: `D5/S3/Analytic/Fourier/ThetaDifferentialKernel.romikPhi_eq_source`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/ThetaDifferentialKernel.romikPhi_eq_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dan Romik (2021). *Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases*. URL: <https://doi.org/10.4064/aa200515-10-3>.

*Commentary.*

For every real x, romikPhi x = sourceThetaKernel x. On the nonnegative axis the convergent series agree term by term; modular evenness extends the identification to negative x.

**Theorem 1.9 (Positive-half-line bounds).**

Lean statement: `D5/S3/Analytic/Fourier/ThetaDifferentialKernel.psi_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/ThetaDifferentialKernel.psi_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dan Romik (2021). *Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases*. URL: <https://doi.org/10.4064/aa200515-10-3>.

*Commentary.*

For x >= 0, both |psi x| and |psiFirst x| are at most sourceThetaKernel x. The weighted-series comparison supplies decay and integrability for integration by parts.

## References

- Truth anchor: `D5/S3/Analytic/Fourier/ThetaDifferentialKernel.hasDerivAt_thetaSeries`
- Truth anchor: `D5/S3/Analytic/Fourier/ThetaDifferentialKernel.omega_eq_series`
- Truth anchor: `D5/S3/Analytic/Fourier/ThetaDifferentialKernel.psi_bounds`
- Truth anchor: `D5/S3/Analytic/Fourier/ThetaDifferentialKernel.psi_deriv_zero`
- Truth anchor: `D5/S3/Analytic/Fourier/ThetaDifferentialKernel.romikPhi_eq_differential`
- Truth anchor: `D5/S3/Analytic/Fourier/ThetaDifferentialKernel.romikPhi_eq_source`
- Truth anchor: `D5/S3/Analytic/Fourier/ThetaDifferentialKernel.romikPhi_even`
- Truth anchor: `D5/S3/Analytic/Fourier/ThetaDifferentialKernel.thetaSeries_local_majorant`
- Truth anchor: `D5/S3/Analytic/Fourier/ThetaDifferentialKernel.thetaSeries_zero`
- Dependency: [D5/S3/Zeros/Jensen/SourceThetaMomentBounds](../../Zeros/Jensen/SourceThetaMomentBounds.md)
