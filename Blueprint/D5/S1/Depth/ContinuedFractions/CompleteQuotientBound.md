# Discriminants Under Mobius Pullback

## Abstract

A Mobius pullback scales a quadratic discriminant by the square of its determinant, so unimodular transfers preserve it.

**Lemma 1.1 (Mobius pullback scales the discriminant).**

$$\forall f: \operatorname{QuadraticCoefficients}, M: \operatorname{MobiusInt},\ \operatorname{discriminant}\left(\operatorname{pullback}\left(f, M\right)\right) = \operatorname{det}\left(M\right)^{2} \cdot \operatorname{discriminant}\left(f\right).$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/CompleteQuotientBound.pullback_discriminant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pullback coefficients result from substituting the inverse linear-fractional relation and clearing its squared denominator. Their discriminant is the original discriminant multiplied by the square of the transfer determinant.

**Theorem 1.2 (Unimodular Mobius transfer preserves the discriminant).**

$$\forall f: \operatorname{QuadraticCoefficients}, M: \operatorname{MobiusInt},\ (\operatorname{det}\left(M\right) = 1 \lor \operatorname{det}\left(M\right) = -1) \Rightarrow \operatorname{discriminant}\left(\operatorname{pullback}\left(f, M\right)\right) = \operatorname{discriminant}\left(f\right).$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/CompleteQuotientBound.unimodular_transform_preserves_discriminant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A unimodular integer Mobius transfer has determinant one or minus one. Its determinant square is therefore one, so the pullback leaves the quadratic discriminant unchanged.

## References

- Truth anchor: `D5/S1/Depth/ContinuedFractions/CompleteQuotientBound.pullback_discriminant`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/CompleteQuotientBound.unimodular_transform_preserves_discriminant`
- Dependency: [D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic](PeriodicImpliesQuadratic.md)
