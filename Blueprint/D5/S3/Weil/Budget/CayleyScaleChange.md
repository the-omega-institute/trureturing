# Cayley Scale Change

## Abstract

Positive Cayley scales are related by an explicit real-parameter disk automorphism.

**Definition 1.1 (Scaled Cayley coordinate).**

$$c_{a}(\xi) = \frac{\xi + ia}{\xi - ia}.$$

*Formalization.* `D5/S3/Weil/Budget/CayleyScaleChange.cayleyCoordinate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate is constructed directly from a real spectral point and a real scale, with values in the complex plane.

**Definition 1.2 (Hyperbolic scale parameter).**

$$r_{a,b} = \frac{a - b}{a + b}.$$

*Formalization.* `D5/S3/Weil/Budget/CayleyScaleChange.scaleChangeParameter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive-scale hypotheses make the denominator nonzero and place this parameter between minus one and one.

**Definition 1.3 (Real disk automorphism).**

$$\operatorname{Phi}(r)(z) = \frac{z + r}{1 + rz}.$$

*Formalization.* `D5/S3/Weil/Budget/CayleyScaleChange.realDiskAutomorphism` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the source's Mobius action with a real parameter.

**Theorem 1.4 (Cayley scale-change law).**

$$\forall a, b, \xi: \mathbb{R}, 0 < a \land 0 < b \Rightarrow\\{}c_{b}(\xi) = \operatorname{Phi}(r_{a,b})(c_{a}(\xi)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/CayleyScaleChange.cayley_scale_change` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof clears only denominators forced nonzero by the two positive scales and then verifies the source's rational identity.

## References

- Truth anchor: `D5/S3/Weil/Budget/CayleyScaleChange.cayleyCoordinate`
- Truth anchor: `D5/S3/Weil/Budget/CayleyScaleChange.cayley_scale_change`
- Truth anchor: `D5/S3/Weil/Budget/CayleyScaleChange.realDiskAutomorphism`
- Truth anchor: `D5/S3/Weil/Budget/CayleyScaleChange.scaleChangeParameter`
