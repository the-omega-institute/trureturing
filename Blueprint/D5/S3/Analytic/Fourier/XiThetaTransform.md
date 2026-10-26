# The theta transform and completed zeta

## Abstract

The theta transform and completed zeta.

The same actual kernel admits a shifted-ray application that detects a nonzero coordinate on the genuine zeta spectrum. Write Phi=romikPhi=sourceThetaKernel, delta=log(2)/2, and J_r(z)=integral_(t>0) Phi^(r)(delta+t)*cos(z*t). There exists an actual index n in zetaZeroData with J_0(zetaZeroData.gamma(n)) nonzero. The spectral parameter is the original complex gamma(n); neither RH nor reality of gamma(n) is assumed.

All derivative and convergence premises are paid for the complete kernel. For every derivative order r and every a>=0, exp(t/2)*abs(Phi^(r)(a+t)) is integrable on t>0 and tends to zero at infinity. The literal mode has the form exp(x/2)*P_r(y)*exp(-y), y=pi*m^2*exp(2x), with P_0=4y^2-6y and P_(r+1)=(1/2-2y)*P_r+2y*P_r'. Split the full series into m=1 and the existing originalTail(1). The existing arbitrary-order tailJet endpoint bounds pay the latter. The first mode uses the quadratic exponential estimate to obtain exp(x/2)*abs(primalJet(r,1,x))<=C_r*exp(-x) for x>=0. Genuine local termwise differentiation and equality on the open positive ray identify these jets with the actual derivatives; no finite-mode substitute or assumed derivative convergence is used.

In the strip abs(Im(z))<=1/2, the elementary exponential formulas bound both abs(cos(z*t)) and abs(sin(z*t)) by exp(t/2). Apply the half-line fundamental theorem to H_r(t)=Phi^(r+1)(delta+t)*cos(z*t)+z*Phi^(r)(delta+t)*sin(z*t), for r=0 and r=2. The paid derivative, integrability and endpoint conditions give J_2+z^2*J_0=-Phi'(delta) and J_4+z^2*J_2=-Phi'''(delta). Thus z^2*(z^2*J_0+Phi'(delta))=Phi'''(delta)+J_4, including z=0. The right side has the uniform norm bound C=abs(Phi'''(delta))+integral_(t>0) exp(t/2)*abs(Phi''''(delta+t)).

At delta every positive mode has y=2*pi*m^2>6, and P_1(y)=-y*(8y^2-30y+15)<0. True summability transfers this sign to Phi'(delta)<0. Put d=-Phi'(delta)>0. The canonical zeta presentation already has finite spectral-radius balls, so one can choose an actual gamma with norm greater than 1+C/d; its nontrivial-zero certificate also places it in the same strip. If J_0(gamma)=0, the exact identity would imply norm(gamma)^2*d<=C, a contradiction. This is a checked application of the existing theta jets, half-line calculus and canonical zero-data interfaces, with no new mathematical declaration or literature-priority claim. The Gaussian interpretation in Suzuki W360 uses the ordinary transform v_delta=2*cPhi*J_0, cPhi=pi^(1/4)/4. A nonzero spectral coordinate alone does not establish nondegeneracy or positivity of the full signed Weil pairing, the original Gamma form-domain, density, or RH.

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

*Citation.* Dan Romik (2021). *Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases*. URL: <https://doi.org/10.4064/aa200515-10-3>.

*Commentary.*

Romik (1.11), with the all-complex convention Xi(z)=xi(1/2+i*z) from (1.3), states this Fourier identity for the all-real Phi of (1.8). The repository identifies Phi with sourceThetaKernel and proves the integral equals xiReading(1/2+i*z) for every complex z using two integrations by parts, reflection, and the symmetric Mellin identity. No division by s*(s-1) occurs, so z=0 and z=plus or minus i/2 are included.

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

The Gaussian dominated even-moment series gives the exact all-jet application to this same normalized source. Put p=sourceThetaDensity, m=Re(xiReading(1/2))>0 and C=(sum thetaMajorant)/m. Continuity and |p(x)|<=C exp(-x^2) follow from the literal density and kernel bound. The Fourier identity at zero identifies xiReading(1/2) with the real number m; dividing the all-complex Fourier identity by this unchanged denominator therefore gives the normalized exponential integral.

The complex cosine is half the sum of the two exponentials. Both normalized exponential integrals at w and -w are absolutely convergent, and the reflection xi(s)=xi(1-s) identifies their values. Thus integral p(x)cos(w*x) dx=xiReading(1/2+i*w)/xiReading(1/2) for every complex w. Taking w=sqrt(z) gives the literal xiSquareSource, globally including zero and branch-cut points. Its kth normalized jet is (-1)^k sourceThetaCoefficient(k). In particular the positive moment coefficients are not the unsigned Taylor coefficients in square coordinates. This source correspondence supplies no individual sourceCoupling sign or Jensen root-reality conclusion.

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
