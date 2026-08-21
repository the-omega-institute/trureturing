# Fractional-Reciprocal Inner Product

## Abstract

A fractional-reciprocal vector has an exact unit-interval inner product.

**Theorem 1.1 (The fractional-reciprocal inner product has an exact Euler value).**

$$\forall a\in\mathbb{Z}, 1 \leq a \Rightarrow \langle\operatorname{unitIntervalIndicator}, \operatorname{integerFractionalReciprocal}(a)\rangle_{L^2(0,\infty)} = \frac{\log a + 1 - \gamma}{a}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/InnerProducts/FractionalReciprocalInnerProduct.fractional_reciprocal_inner_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is the real L2 space on the positive half-line. The first vector is the indicator of the open unit interval, and the second is the L2 class of x mapped to fract(1/(a x)). A positive integer is transported through its equal natural representative, and both vectors are constructed from those source functions.

Square integrability follows from boundedness near zero and reciprocal-square decay after one. A reciprocal change of variables reduces the inner product to the fractional-part tail integral.

The intervals from n+1 to n+2 identify that tail directly with Mathlib's ZetaAsymptotics.term series. Its exact sum is one minus the Euler-Mascheroni constant; the initial interval contributes log a.

## References

- Truth anchor: `D5/S3/Constants/InnerProducts/FractionalReciprocalInnerProduct.fractional_reciprocal_inner_product`
