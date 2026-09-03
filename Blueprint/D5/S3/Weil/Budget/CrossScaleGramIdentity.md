# Cross-Scale Gram Identity

## Abstract

Integer moments at one positive Cayley scale are Gram pairings of the explicit rational features transported from another positive scale.

**Theorem 1.1 (Transported moments are rational-feature Gram pairings).**

$$\begin{aligned}\forall nu: \operatorname{Measure}\left(\mathbb{R}\right), a: \mathbb{R}, b: \mathbb{R}, j: \mathbb{N}, k: \mathbb{N},\\0 < a \land 0 < b \Rightarrow\\\operatorname{let} r: \mathbb{R} := \frac{a - b}{a + b},\\\operatorname{let} m: \mathbb{R} \to \mathbb{Z} \to \mathbb{C} := (s: \mathbb{R}, n: \mathbb{Z}) \mapsto \operatorname{integral}\left(\operatorname{cayleySpectralMeasure}\left(nu, s\right), (z: \mathbb{C}) \mapsto z^{n}\right),\\\operatorname{let} e: \mathbb{N} \to \mathbb{C} \to \mathbb{C} := (ell: \mathbb{N}, z: \mathbb{C}) \mapsto \frac{\operatorname{sqrt}\left(1 - r^{2}\right)}{1 + r \cdot z} \cdot \left(\phi_{r}\right)\left(z\right)^{ell},\\m\left(b, j - k\right) = \frac{a}{b} \cdot \operatorname{integral}\left(\operatorname{cayleySpectralMeasure}\left(nu, a\right), (z: \mathbb{C}) \mapsto e\left(j, z\right) \cdot \overline{e\left(k, z\right)}\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/CrossScaleGramIdentity.cross_scale_gram_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement constructs the scale parameter, every integer moment, and every rational feature from the supplied positive real measure and the canonical Cayley primitives.

The proof applies positive Cayley scale transport and then identifies its density pointwise with the product of a feature and the complex conjugate of a second feature.

## References

- Truth anchor: `D5/S3/Weil/Budget/CrossScaleGramIdentity.cross_scale_gram_identity`
- Dependency: [D5/S3/Weil/Budget/PositiveCayleyScaleTransport](PositiveCayleyScaleTransport.md)
