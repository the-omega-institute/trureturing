# Reflected-Pair Signed Distance

## Abstract

A reflected pair becomes a negative signed distance in the squared normal coordinate.

**Theorem 1.1 (A reflected pair gives a negative signed-distance resolvent).**

$$\forall \delta, r, u: \mathbb{R},\\{}(0 < \delta) \land (u \neq \delta^{2}) \Rightarrow\\{}(-\delta^{2} < 0 \land\\{}(r - \delta)(r + \delta) = r^{2} - \delta^{2} \land\\{}((r - \delta)(r + \delta))^{2} = (r^{2} - \delta^{2})^{2} \land\\{}\operatorname{deriv}(v \mapsto (v - \delta^{2})^{2})(u) / (u - \delta^{2})^{2} = 2 / (u - \delta^{2})).$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ReflectedPairSignedDistance.reflected_pair_signed_distance_resolvent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive delta, the reflected offsets minus delta and delta determine the negative signed support point minus delta squared. Their product is r squared minus delta squared, and squaring that product agrees with the squared-coordinate intensity at r squared.

When u differs from delta squared, the same squared intensity is away from its pole and its logarithmic slope is two divided by u minus delta squared. This is only a finite algebraic separation model; it asserts no converse and no connection to xi or spectral data.

## References

- Truth anchor: `D5/S3/Zeros/ReflectedPairSignedDistance.reflected_pair_signed_distance_resolvent`
