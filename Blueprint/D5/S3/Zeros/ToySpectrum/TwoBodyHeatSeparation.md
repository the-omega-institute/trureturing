# Two-Body Heat Separation

## Abstract

After its collision time, the two-body quadratic heat model has two distinct real roots whose squared separation grows linearly with slope eight.

**Theorem 1.1 (The split roots have squared separation eight t minus four c zero).**

$$\forall c_0, t \in \mathbb{R},\ (\frac{c_0}{2} < t) \Rightarrow \operatorname{roots}(\operatorname{twoBodyHeatPolynomial}(c_0, t)) = \{\sqrt{2t - c_0}, -\sqrt{2t - c_0}\} \land \sqrt{2t - c_0} \neq -\sqrt{2t - c_0} \land (\sqrt{2t - c_0} - {-\sqrt{2t - c_0}})^{2} = 8t - 4c_0$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ToySpectrum/TwoBodyHeatSeparation.two_body_heat_real_root_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The heat parameter is c zero minus twice t. Once t is strictly greater than c zero divided by two, the existing quadratic-collision certificate identifies the roots as plus and minus the square root of two t minus c zero and proves that they are distinct.

Mathlib's square-root square theorem then gives the exact squared gap eight t minus four c zero, so its post-collision slope is eight.

This closes only the post-collision real-root and squared-separation clause of the source atom's two-body law. The gas computation, finite-extinction claim, zeta-zero interpretation, and physical-time interpretation are not formalized or claimed here.

## References

- Truth anchor: `D5/S3/Zeros/ToySpectrum/TwoBodyHeatSeparation.two_body_heat_real_root_separation`
- Dependency: [D5/S3/Zeros/ToySpectrum/QuadraticCollisionModel](QuadraticCollisionModel.md)
