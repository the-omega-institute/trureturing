# Complex Moments of a Real Gaussian Density

## Abstract

Explicit complex moments of an arbitrary real Gaussian density are obtained from its entire moment generating function.

**Theorem 1.1 (Integrability of every tilted monomial).**

$$\forall mu \in \mathbb{R},\; \forall v \in \mathbb{R},\; 0< v \Rightarrow \left(\forall n \in N,\; \forall z \in C,\; \operatorname{Integrable}\left(\operatorname{densityMonomial}\left(mu, v, n, z\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianComplexMoments.density_monomial_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real mean, positive real variance, natural degree and complex tilt, the corresponding complex Gaussian density monomial is Bochner integrable. The statement carries no moment or integrability premise beyond positivity of the variance.

**Theorem 1.2 (Zeroth tilted moment).**

$$\forall mu \in \mathbb{R},\; \forall v \in \mathbb{R},\; 0< v \Rightarrow \left(\forall z \in C,\; \operatorname{integral}\left(\operatorname{densityMonomial}\left(mu, v, 0, z\right)\right) = \operatorname{gaussianMGF}\left(mu, v, z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianComplexMoments.density_moment_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integral of the tilted Gaussian density equals the explicit entire Gaussian moment generating function.

**Theorem 1.3 (First tilted moment).**

$$\forall mu \in \mathbb{R},\; \forall v \in \mathbb{R},\; 0< v \Rightarrow \left(\forall z \in C,\; \operatorname{integral}\left(\operatorname{densityMonomial}\left(mu, v, 1, z\right)\right) = \operatorname{mul}\left(\operatorname{tiltedMean}\left(mu, v, z\right), \operatorname{gaussianMGF}\left(mu, v, z\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianComplexMoments.density_moment_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiating the entire Gaussian moment generating function once gives the exact first tilted moment.

**Theorem 1.4 (Second tilted moment).**

$$\forall mu \in \mathbb{R},\; \forall v \in \mathbb{R},\; 0< v \Rightarrow \left(\forall z \in C,\; \operatorname{integral}\left(\operatorname{densityMonomial}\left(mu, v, 2, z\right)\right) = \operatorname{mul}\left(\operatorname{add}\left(\operatorname{pow}\left(\operatorname{tiltedMean}\left(mu, v, z\right), 2\right), v\right), \operatorname{gaussianMGF}\left(mu, v, z\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianComplexMoments.density_moment_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A second differentiation gives the exact second tilted moment, including the variance correction term.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianComplexMoments.density_moment_one`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianComplexMoments.density_moment_two`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianComplexMoments.density_moment_zero`
- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianComplexMoments.density_monomial_integrable`
