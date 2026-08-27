# Monster Primitive Mobius Recovery

## Abstract

Mobius inversion recovers primitive coefficients from logarithmic histories.

**Theorem 1.1 (Logarithmic histories determine every primitive coefficient).**

$$\forall I \in Type, H \in I \to \left(\mathbb{N} \to \mathbb{Q}\right), L \in I \to \left(\mathbb{N} \to \mathbb{Q}\right),\; \left(\forall ray \in I, n \in \mathbb{N},\; n > 0 \Rightarrow \sum_{d \mid n} d \cdot H\left(ray, d\right) = n \cdot L\left(ray, n\right)\right) \Rightarrow \left(\forall ray \in I, n \in \mathbb{N},\; n > 0 \Rightarrow H\left(ray, n\right) = \sum_{k \cdot r = n} \frac{\mu(k)}{k} \cdot L\left(ray, r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Dilation/MonsterPrimitiveMobiusRecovery.monster_primitive_mobius_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let I index the primitive root rays. The functions H and L record the rational coefficients at positive multiples of every ray in the primitive heat series and the negative logarithmic denominator.

The hypothesis is the coefficient form of the logarithmic expansion: multiplying degree n by the source factor 1/k turns it into the displayed divisor sum.

Pinned Mathlib supplies divisor-sum Mobius inversion. Applying it to the degree-scaled coefficients and cancelling positive n gives exactly the factor mu(k)/k in the recovery formula.

## References

- Truth anchor: `D5/S3/Analytic/Dilation/MonsterPrimitiveMobiusRecovery.monster_primitive_mobius_recovery`
