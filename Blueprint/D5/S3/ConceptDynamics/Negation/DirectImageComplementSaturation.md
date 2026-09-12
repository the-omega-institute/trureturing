# Direct Image Complement Saturation

## Abstract

Surjective images preserve complements exactly on unions of whole fibers.

**Theorem 1.1 (Direct image preserves complement exactly on saturated sets).**

$$\forall X, B: \operatorname{Type},\\{}f: X \to B, A: \operatorname{Set}\left(X\right),\\{}\operatorname{Surjective}\left(f\right) \Rightarrow (\operatorname{image}\left(f, \operatorname{complement}\left(A\right)\right) = \operatorname{complement}\left(\operatorname{image}\left(f, A\right)\right) \iff A = \operatorname{preimage}\left(f, \operatorname{image}\left(f, A\right)\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Negation/DirectImageComplementSaturation.image_complement_iff_saturated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f map the source carrier X onto the output carrier B, and let A be any subset of X. The complements are taken in X and B, respectively. No finiteness or injectivity assumption is required.

The equation A = preimage(f, image(f, A)) says that each readout fiber is either entirely selected or entirely excluded. In this case the image of the excluded states is exactly the excluded output set.

Conversely, if a selected and an excluded state share a readout, that readout belongs to both images. The complement equation rules out such a mixed fiber, so the selected set must be saturated.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Negation/DirectImageComplementSaturation.image_complement_iff_saturated`
