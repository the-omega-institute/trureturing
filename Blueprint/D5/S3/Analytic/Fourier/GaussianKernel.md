# Gaussian kernels

## Abstract

Normalized Gaussian kernels and their cosine averages.

**Theorem 1.1 (Expanding the vertical Gaussian exponent).**

Lean statement: `D5/S3/Analytic/Fourier/GaussianKernel.bromwich_exponent`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/GaussianKernel.bromwich_exponent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real M, c, v, and t, the vertical Gaussian exponent expands into its quadratic, linear, and constant terms in t.

**Theorem 1.2 (Gaussian probability densities).**

Lean statement: `D5/S3/Analytic/Fourier/GaussianKernel.q_laws`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/GaussianKernel.q_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive M, q(M,v)=M exp(-M²v²/2)/sqrt(2 pi) is nonnegative and integrable on the real line, with integral one. Scaling the Gaussian integral supplies the normalization.

**Theorem 1.3 (Angular Gaussian transform).**

Lean statement: `D5/S3/Analytic/Fourier/GaussianKernel.q_aft`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/GaussianKernel.q_aft` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cosine transform of q(M,·) at t is exp(-t²/(2M²)), and its sine transform vanishes. These are the real and imaginary parts of the complex Gaussian integral with angular frequency t.

**Theorem 1.4 (Absolute convergence on vertical lines).**

Lean statement: `D5/S3/Analytic/Fourier/GaussianKernel.q_bromwich_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/GaussianKernel.q_bromwich_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive M and arbitrary real c and v, the exponential of (c+it)v+(c+it)²/(2M²) is integrable as a function of t. Its exponent is a quadratic polynomial with negative real leading coefficient.

**Theorem 1.5 (Gaussian inversion on vertical lines).**

Lean statement: `D5/S3/Analytic/Fourier/GaussianKernel.q_bromwich`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/GaussianKernel.q_bromwich` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive M, q(M,v) equals one divided by 2 pi times the integral over real t of exp((c+it)v+(c+it)²/(2M²)), for every real c. Completing the square evaluates the integral and cancels the dependence on c.

**Theorem 1.6 (Gaussian convolution of a cosine).**

Lean statement: `D5/S3/Analytic/Fourier/GaussianKernel.q_cos_convolution`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/GaussianKernel.q_cos_convolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The convolution of cos(gamma u) with q(M,y-u) is exp(-gamma²/(2M²)) cos(gamma y). Translation and the cosine subtraction identity reduce the formula to the cosine and sine transforms.

**Theorem 1.7 (The half-line correction).**

Lean statement: `D5/S3/Analytic/Fourier/GaussianKernel.gaussian_halfline_correction`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/GaussianKernel.gaussian_halfline_correction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For M and y at least one and positive gamma, the absolute integral over v at least zero of cos(gamma v)q(M,y+v) is at most 2M²yq(M,y)/gamma². Integrating twice by parts leaves a cosine average of the second derivative. That derivative is nonnegative on this half-line and has total mass M²yq(M,y); the Gaussian and its first derivative vanish at infinity.

## References

- Truth anchor: `D5/S3/Analytic/Fourier/GaussianKernel.bromwich_exponent`
- Truth anchor: `D5/S3/Analytic/Fourier/GaussianKernel.gaussian_halfline_correction`
- Truth anchor: `D5/S3/Analytic/Fourier/GaussianKernel.q_aft`
- Truth anchor: `D5/S3/Analytic/Fourier/GaussianKernel.q_bromwich`
- Truth anchor: `D5/S3/Analytic/Fourier/GaussianKernel.q_bromwich_integrable`
- Truth anchor: `D5/S3/Analytic/Fourier/GaussianKernel.q_cos_convolution`
- Truth anchor: `D5/S3/Analytic/Fourier/GaussianKernel.q_laws`
- Dependency: [D5/S3/Analytic/Fourier/AngularFejerKernel](AngularFejerKernel.md)
