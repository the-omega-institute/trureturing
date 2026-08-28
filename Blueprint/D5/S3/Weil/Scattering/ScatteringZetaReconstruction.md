# Scattering-Zeta Reconstruction

## Abstract

All shifted normalized modular-scattering readings reconstruct the Riemann zeta value.

**Theorem 1.1 (The shifted scattering products converge to zeta).**

$$\forall z \in \mathbb{C},\ \Re(z) > 1 \Rightarrow \lim_{N\to\infty} \prod_{j=0}^{N-1} \frac{\zeta(2 \cdot \frac{z + j + 1}{2} - 1)}{\zeta(2 \cdot \frac{z + j + 1}{2})} = \zeta(z) \land \lim_{N\to\infty} \prod_{j=0}^{N-1} \frac{\sqrt{\pi} \cdot \Gamma(\frac{z + j + 1}{2} - \frac{1}{2})}{\Gamma(\frac{z + j + 1}{2})} \cdot \frac{\zeta(2 \cdot \frac{z + j + 1}{2} - 1)}{\zeta(2 \cdot \frac{z + j + 1}{2})} \cdot \frac{\Gamma(\frac{z + j + 1}{2})}{\sqrt{\pi} \cdot \Gamma(\frac{z + j}{2})} = \zeta(z)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Scattering/ScatteringZetaReconstruction.scattering_zeta_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex z with real part greater than one, the first displayed factor is the normalized zeta ratio at the shifted half-argument. Its finite products telescope exactly to zeta(z) divided by zeta(z+N).

A vertical-translate L-series with unit-modulus coefficients proves that zeta(z+N) tends to one for arbitrary fixed imaginary part. Gamma nonvanishing on the relevant right half-plane then cancels the Archimedean factors in the second displayed product.

## References

- Truth anchor: `D5/S3/Weil/Scattering/ScatteringZetaReconstruction.scattering_zeta_reconstruction`
