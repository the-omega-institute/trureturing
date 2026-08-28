# Vertical Attenuation Tomography

## Abstract

A finite logarithmic modulus profile is the sum of its one-factor vertical attenuations.

**Theorem 1.1 (Vertical attenuation is additive over the finite zero family).**

$$\forall IndexType: \operatorname{Type}, \operatorname{Fintype}\left(IndexType\right) \Rightarrow \forall A: \mathbb{R} \to \mathbb{R}, \forall profile: \mathbb{R} \to \left(\mathbb{R} \to \mathbb{R}\right), \forall factor: IndexType \to \left(\mathbb{R} \to \left(\mathbb{R} \to \mathbb{R}\right)\right), \forall realPart: IndexType \to \mathbb{R}, \forall hA: \forall y: \mathbb{R}, A(y) = \frac{1}{4 \pi} \times \int_{\mathbb{R}} profile(x)(y) dx, \forall hdecomp: \forall x: \mathbb{R}, \forall y: \mathbb{R}, profile(x)(y) = \sum_{i: IndexType} factor(i)(x)(y), \forall hintegrable: \forall i: IndexType, \forall y: \mathbb{R}, \operatorname{Integrable}\left((x: \mathbb{R} \mapsto factor(i)(x)(y))\right), \forall hone: \forall i: IndexType, \forall y: \mathbb{R}, 0 < y \Rightarrow \frac{1}{4 \pi} \times \int_{\mathbb{R}} factor(i)(x)(y) dx = \operatorname{min}\left(y, realPart(i)\right), \forall y: \mathbb{R}, 0 < y \Rightarrow A(y) = \sum_{i: IndexType} \operatorname{min}\left(y, realPart(i)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/VerticalAttenuation/VerticalAttenuation.vertical_attenuation_tomography` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real-line profile, its one-factor decomposition, and the finite factor integrability are public source laws. The one-factor Bode identity gives min(y, realPart i) after the 1/(4 pi) normalization.

Finite-sum linearity of the Bochner integral then yields the exact modulus-only tomography formula for every positive height y.

## References

- Truth anchor: `D5/S3/Weil/VerticalAttenuation/VerticalAttenuation.vertical_attenuation_tomography`
