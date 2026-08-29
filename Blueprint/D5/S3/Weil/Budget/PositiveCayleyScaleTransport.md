# Positive Cayley Scale Transport

## Abstract

Resolvent-weighted Cayley spectral measures obey the explicit positive pushforward law under a change of scale.

**Definition 1.1 (Resolvent-weighted source measure).**

$$\forall nu: \operatorname{Measure}\left(\mathbb{R}\right), a: \mathbb{R}, W_{a}(nu) = \operatorname{withDensity}\left(nu, xi \mapsto \operatorname{ofReal}\left(\frac{1}{xi^{2} + a^{2}}\right)\right).$$

*Formalization.* `D5/S3/Weil/Budget/PositiveCayleyScaleTransport.resolventWeightedMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The density is constructed directly from the real spectral variable and the positive resolvent denominator.

**Definition 1.2 (Cayley spectral measure).**

$$\forall nu: \operatorname{Measure}\left(\mathbb{R}\right), a: \mathbb{R}, mu_{a}(nu) = \operatorname{map}\left(c_{a}, W_{a}(nu)\right).$$

*Formalization.* `D5/S3/Weil/Budget/PositiveCayleyScaleTransport.cayleySpectralMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the actual pushforward of the resolvent-weighted source measure by the scale-dependent Cayley coordinate.

**Definition 1.3 (Positive scale-transport weight).**

$$\forall a, b: \mathbb{R}, z: \mathbb{C}, q_{a,b}(z) = \frac{{1 + r_{a,b}} \cdot {1 + r_{a,b}}}{\operatorname{normSq}\left(1 + r_{a,b} \cdot z\right)}.$$

*Formalization.* `D5/S3/Weil/Budget/PositiveCayleyScaleTransport.scaleTransportWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real weight is the source's explicit norm-square quotient.

**Theorem 1.4 (Positive scale transport).**

$$\forall nu: \operatorname{Measure}\left(\mathbb{R}\right), a, b: \mathbb{R}, 0 < a \land 0 < b \Rightarrow\\{}mu_{b}(nu) = \operatorname{map}\left(\operatorname{Phi}(r_{a,b}), \operatorname{withDensity}\left(mu_{a}(nu), z \mapsto \operatorname{ofReal}\left(q_{a,b}(z)\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/PositiveCayleyScaleTransport.positive_cayley_scale_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof combines the pointwise resolvent-density identity with the Cayley scale-change law and functoriality of measure maps.

## References

- Truth anchor: `D5/S3/Weil/Budget/PositiveCayleyScaleTransport.cayleySpectralMeasure`
- Truth anchor: `D5/S3/Weil/Budget/PositiveCayleyScaleTransport.positive_cayley_scale_transport`
- Truth anchor: `D5/S3/Weil/Budget/PositiveCayleyScaleTransport.resolventWeightedMeasure`
- Truth anchor: `D5/S3/Weil/Budget/PositiveCayleyScaleTransport.scaleTransportWeight`
- Dependency: [D5/S3/Weil/Budget/CayleyScaleChange](CayleyScaleChange.md)
