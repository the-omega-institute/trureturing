# Short Affine Bands under Independent Uniform Perturbations

## Abstract

The Euclidean norm of the scaled coefficients controls near-collision probability.

Let J be finite. Each coordinate x(j) is independently uniform on [−r(j),r(j)] with r(j)>0. For real a(j) and b set c(j)=a(j)r(j), and let S>0 be the sum of c(j)². For η≥0 write P(η) for the probability of |Σ a(j)x(j)+b|≤η. Write B(η)=exp(1/2)√(15π/2)η/√S.

**Theorem 1.1 (An interval probability bound with Euclidean scaling).**

$$\operatorname{P}\left(eta\right) \le \operatorname{min}\left(1, \operatorname{B}\left(eta\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/UniformPerturbationEuclidean.intervalNoise_pi_affine_le_euclidean` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fubini factors the characteristic function of the sum into sinc(c(j)t). When the fourth-power sum is at most S²/2, the reciprocal quadratic envelope with coefficient S/15 controls the modulus. The Gaussian window bound applies at center −b on the law of the same sum, and yields B(η).

If the fourth-power condition fails, at least one c(j)² exceeds S/2. Conditioning on the other coordinates gives a probability at most the interval length ratio η/|c(j)|, bounded by √2η/√S. At zero resolution use the same conditioning argument with any nonzero coefficient. The probability is also bounded by one.

This estimate concerns the product law on the admitted intervals. The center shift leaves the coefficient scale unchanged. In a collision test the coefficients are the differences of the degree vectors and the perturbation coordinates are shared.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/UniformPerturbationEuclidean.intervalNoise_pi_affine_le_euclidean`
- Dependency: [D5/S3/Fourier/Concentration/ContinuousSpectralPerturbations](ContinuousSpectralPerturbations.md)
- Dependency: [D5/S3/Fourier/Concentration/DiffuseSincProduct](DiffuseSincProduct.md)
- Dependency: [D5/S3/Fourier/Concentration/GaussianCharacteristicWindow](GaussianCharacteristicWindow.md)
