# Multiplicative Digit Invariant

## Abstract

The contraction reading is additive on coprimes, signed by digit shape, and splits off zeta.

Three properties of the contraction reading were proved separately and never stated together: additivity over coprime factors, the sign rule fixed by the parity of the least occupied Zeckendorf index, and the Dirichlet factorisation into zeta times the prime-axis series.

This document adds exactly one thing: the conjunction. Each conjunct is the existing theorem transcribed word for word, with its implicit binders made explicit; nothing is weakened and nothing new is proved. The reason the conjunction is worth a declaration is that the source sentence is a single claim about one invariant, and separate parts do not stand in for it: what carries a compound sentence is a node, not a set of pieces.

Read together the three say why the reading deserves the name invariant. It is additive where the prime supports are disjoint, so it is a homomorphism off the common factors. Its sign does not track magnitude but the parity of one digit position. And its Dirichlet series carries the arithmetic of the integers in the zeta factor while the digit structure sits entirely in the prime-axis factor.

**Theorem 1.1 (The contraction reading is a multiplicative digit invariant).**

$$\forall m, n\in \mathbb{N},\ \operatorname{gcd}(m, n) = 1 \Rightarrow\ lambda_{minus}(m \cdot n) = lambda_{minus}(m) + lambda_{minus}(n).$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/MultiplicativeDigitInvariant.lambda_minus_is_a_multiplicative_digit_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed conjunct is coprime additivity; the package also carries the least-index sign rule and the zeta factorisation.

## References

- Truth anchor: `D5/S3/Axis/MultiplicativeDigitInvariant.lambda_minus_is_a_multiplicative_digit_invariant`
- Dependency: [D5/S1/Deficit/LambdaMinusAdditive](../../S1/Deficit/LambdaMinusAdditive.md)
- Dependency: [D5/S3/Axis/LambdaMinusDirichletSeries](LambdaMinusDirichletSeries.md)
