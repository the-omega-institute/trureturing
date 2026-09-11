# Polynomial Exponent Divisibility for Vanishing Diagonals

## Abstract

Polynomial exponents divide their vanishing-diagonal coefficients.

**Theorem 1.1 (Polynomial exponent theorem).**

$$\forall P: Polynomial \mathbb{Z}, ((\operatorname{eval}\left(P, 1\right) = 1) \land (\forall n: \mathbb{N}, (1 \le n) \implies (1 \le \operatorname{eval}\left(P, n\right)))) \implies (\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{eval}\left(P, n\right) \mid \operatorname{a}\left(\operatorname{fun}\left(m, \operatorname{toNat}\left(\operatorname{eval}\left(P, m\right)\right)\right), n\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/PolynomialExponentSelfDivisibility.polynomial_exponent_self_divisibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive integer polynomial exponents normalized at one divide their coefficients.

**Theorem 1.2 (Affine polynomial instance).**

$$\forall d: \mathbb{N},  \forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{eval}\left(\operatorname{C}\left(d\right) * (X - 1) + 1, n\right) \mid \operatorname{a}\left(d + 1, n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/PolynomialExponentSelfDivisibility.affine_polynomial_exponent_self_divisibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The affine polynomial instance recovers the frozen affine theorem, including slope zero.

**Theorem 1.3 (Monomial polynomial instance).**

$$\forall k: \mathbb{N},  \forall n: \mathbb{N}, (1 \le n) \implies ((n) ^ k \mid \operatorname{a}\left(\operatorname{fun}\left(m, m ^ k\right), n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/PolynomialExponentSelfDivisibility.monomial_exponent_self_divisibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The monomial instance follows from the polynomial theorem.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/PolynomialExponentSelfDivisibility.affine_polynomial_exponent_self_divisibility`
- Truth anchor: `D5/S1/Recurrence/Residue/PolynomialExponentSelfDivisibility.monomial_exponent_self_divisibility`
- Truth anchor: `D5/S1/Recurrence/Residue/PolynomialExponentSelfDivisibility.polynomial_exponent_self_divisibility`
- Dependency: [D5/S1/Recurrence/Residue/DiagonalExponentSelfDivisibility](DiagonalExponentSelfDivisibility.md)
