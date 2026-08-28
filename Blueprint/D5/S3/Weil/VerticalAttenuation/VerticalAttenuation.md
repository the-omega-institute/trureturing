# Vertical Attenuation Tomography

## Abstract

A finite logarithmic modulus profile is the sum of its one-factor vertical attenuations.

**Theorem 1.1 (Vertical attenuation is additive over the finite zero family).**

$$\forall IndexType: Type, \operatorname{Fintype}\left(IndexType\right) \Rightarrow \forall A, \forall profile, \forall factor, \forall realPart, \forall x \in \mathbb{R}, y \in \mathbb{R},\; profile(x)(y) = \operatorname{finiteFactorSum}\left(factor, x, y\right) \Rightarrow 0 < y \Rightarrow A(y) = \sum_{i\in\operatorname{Fintype}\left(IndexType\right)} \operatorname{min}\left(y, realPart(i)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/VerticalAttenuation/VerticalAttenuation.vertical_attenuation_tomography` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real-line profile, its one-factor decomposition, and the finite factor integrability are public source laws. The one-factor Bode identity gives min(y, realPart i) after the 1/(4 pi) normalization.

Finite-sum linearity of the Bochner integral then yields the exact modulus-only tomography formula for every positive height y.

## References

- Truth anchor: `D5/S3/Weil/VerticalAttenuation/VerticalAttenuation.vertical_attenuation_tomography`
