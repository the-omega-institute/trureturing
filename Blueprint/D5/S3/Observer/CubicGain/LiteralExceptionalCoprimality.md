# The exceptional factor in the literal source identity

## Abstract

FC and the displayed exceptional factor

F is the original criticalPolynomial, with precisely the sixty-eight integer coefficients FC. Write H over any commutative coefficient ring for X^90 (2X+1)^5 (5X+2)^14 (8X-1)^20 (X^2+8X+4)^2; exceptionalFactor is this expression. This is exactly the polynomial displayed on the right of the proposed h identity in VI, Lemma 4.2. No parameter or root is selected.

**Definition 1.1 (The displayed exceptional polynomial).**

Lean statement: `D5/S3/Observer/CubicGain/LiteralExceptionalCoprimality.exceptionalFactor`

*Formalization.* `D5/S3/Observer/CubicGain/LiteralExceptionalCoprimality.exceptionalFactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any commutative coefficient ring R, exceptionalFactor in R[X] is the displayed expression H above, using the same exponents and integer coefficients.

**Theorem 1.2 (The displayed degree-133 factor is coprime to FC).**

$$\operatorname{natDegree}(H_{\mathbb{Z}})= 133\land \operatorname{IsCoprime}(F, H_{\mathbb{R}})$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/LiteralExceptionalCoprimality.displayed_exceptional_factor_coprime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integer polynomial H has natural degree 133, and its real coefficient image is coprime to F. Thus no zero of F is a zero of H. The square-free product G=X (2X+1) (5X+2) (8X-1) (X^2+8X+4) has degree six. Explicit integer polynomials U,V,W satisfy U F+V G=1+101 W. Reduction modulo 101 preserves degrees 67 and six and proves a nonzero fixed-degree resultant. Coefficient maps transfer this nonvanishing to the rationals; the resultant criterion and extension to the reals give coprimality with G. Splitting the five factors and restoring their original powers proves the assertion for H.

This result concerns the exact displayed H. The identity H=pp_positive(gcd(a0,c0)) for the original fixed minors has not been established here. Consequently it does not identify the actual gcd, determine the reduced a and c, or settle their degrees, their coprimalities with F, the degree-sixty quotients, or root and world exhaustion.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/LiteralExceptionalCoprimality.displayed_exceptional_factor_coprime`
- Truth anchor: `D5/S3/Observer/CubicGain/LiteralExceptionalCoprimality.exceptionalFactor`
- Dependency: [D5/S3/Observer/CubicGain/LiteralCriticalCoprimality](LiteralCriticalCoprimality.md)
