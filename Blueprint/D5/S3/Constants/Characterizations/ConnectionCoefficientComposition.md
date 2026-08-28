# Connection Coefficient Composition

## Abstract

Connection coefficients compose multiplicatively along a two-step path.

**Theorem 1.1 (Connection coefficients multiply along composition).**

$$(\forall R, M: Type, (\operatorname{CommSemiring}(R) \land \operatorname{AddCommMonoid}(M) \land \operatorname{Module}(R, M)) \Rightarrow \forall a, b: R, X, Y, Z: M, (Y = a \cdot X \land Z = b \cdot Y) \Rightarrow Z = {a \times b} \cdot X) \land\\{}(\forall x \in \mathbb{R}, 0 < x \Rightarrow \sqrt{\frac{\pi \times \operatorname{exp}(x)}{2 \times x}} = \sqrt{\frac{\pi}{2}} \times \operatorname{exp}(\frac{x}{2}) \times x^{-\frac{1}{2}}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Characterizations/ConnectionCoefficientComposition.connection_coefficient_composition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first clause quantifies the scalar and module carriers and states both successive path equations before deriving the product coefficient. Commutativity presents the coefficient in source order.

The second clause exposes the displayed positive-real certificate. The strictly positive x premise is the domain on which the reciprocal square-root scale is defined and the three factors multiply exactly.

## References

- Truth anchor: `D5/S3/Constants/Characterizations/ConnectionCoefficientComposition.connection_coefficient_composition`
