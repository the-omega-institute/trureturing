# The A157100 Catalan transform

## Abstract

The five-term recurrence for the Catalan transform A157100.

Work in ordinary formal power series over the rational numbers. The symbol c denotes Mathlib's natural Catalan series, mapped coefficientwise by the canonical homomorphism to Q. Its application to a series with zero constant coefficient denotes formal substitution. All sequence indices are natural; subtraction in a sequence argument is natural truncated subtraction. All polynomial scalars in the recurrence are evaluated in Q.

**Definition 1.1 (The source generating function).**

$$A = (1 + X) \cdot \operatorname{c}\left(X \cdot (1 - X^{2})\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/MatharA157100FiveTermRecurrence.A` (`✓ std3`).

*Citation.* R. J. Mathar; Paul Barry; OEIS Foundation Inc. (2015). *OEIS A157100 — five-term recurrence for a Catalan transform*. URL: <https://oeis.org/A157100>.

*Commentary.*

OEIS A157100 FORMULA gives (1+x)*c(x*(1-x^2)), with c the generating function of A000108. Formal substitution is defined because X*(1-X^2) has constant coefficient zero.

**Definition 1.2 (The offset-zero coefficients).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, A\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/MatharA157100FiveTermRecurrence.a` (`✓ std3`).

*Citation.* R. J. Mathar; Paul Barry; OEIS Foundation Inc. (2015). *OEIS A157100 — five-term recurrence for a Catalan transform*. URL: <https://oeis.org/A157100>.

*Commentary.*

OEIS OFFSET 0,2 assigns index zero to the first coefficient. The rational representation is the coefficient sequence of this exact generating function.

**Definition 1.3 (Mathar's five-term assertion).**

$$claim \Leftrightarrow \left(\forall n \in \mathbb{N},\; 4 \le n \Rightarrow ((n:\mathbb{Q}) + 1) \cdot \operatorname{a}\left(n\right) + (-5 \cdot (n:\mathbb{Q}) + 1) \cdot \operatorname{a}\left(n - 1\right) + 2 \cdot (2 \cdot (n:\mathbb{Q}) - 1) \cdot \operatorname{a}\left(n - 2\right) + 2 \cdot (2 \cdot (n:\mathbb{Q}) - 7) \cdot \operatorname{a}\left(n - 3\right) + 2 \cdot (-2 \cdot (n:\mathbb{Q}) + 7) \cdot \operatorname{a}\left(n - 4\right) = 0\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/MatharA157100FiveTermRecurrence.claim` (`✓ std3`).

*Citation.* R. J. Mathar; Paul Barry; OEIS Foundation Inc. (2015). *OEIS A157100 — five-term recurrence for a Catalan transform*. URL: <https://oeis.org/A157100>.

*Commentary.*

The immutable OEIS record attributes the displayed identity to R. J. Mathar, February 5, 2015. The source does not state an onset. Here n ≥ 4 is the maximal well-formed interpretation under its offset-zero convention, not a quoted hypothesis. Every such n is included; no eventual or finite-prefix substitute is used.

**Theorem 1.4 (The five-term recurrence).**

$$\forall n \in \mathbb{N},\; 4 \le n \Rightarrow ((n:\mathbb{Q}) + 1) \cdot \operatorname{a}\left(n\right) + (-5 \cdot (n:\mathbb{Q}) + 1) \cdot \operatorname{a}\left(n - 1\right) + 2 \cdot (2 \cdot (n:\mathbb{Q}) - 1) \cdot \operatorname{a}\left(n - 2\right) + 2 \cdot (2 \cdot (n:\mathbb{Q}) - 7) \cdot \operatorname{a}\left(n - 3\right) + 2 \cdot (-2 \cdot (n:\mathbb{Q}) + 7) \cdot \operatorname{a}\left(n - 4\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/MatharA157100FiveTermRecurrence.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; Paul Barry; OEIS Foundation Inc. (2015). *OEIS A157100 — five-term recurrence for a Catalan transform*. URL: <https://oeis.org/A157100>.

*Commentary.*

Apply the existing Catalan differential identity at t=X*(1-X^2) and use the formal chain and product rules for A=(1+X)*c(t). Polynomial normalization gives (1-5X+4X^2+4X^3-4X^4)*(X*A')+(1-4X+6X^2-2X^3-2X^4)*A=1-3X^2. For every n ≥ 4 the forcing coefficient vanishes. The existing Euler coefficient identity and the four shifts yield exactly the five displayed terms. No Hankel-transform or Somos-4 assertion is part of this theorem.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/MatharA157100FiveTermRecurrence.A`
- Truth anchor: `D5/S1/Recurrence/Algebraic/MatharA157100FiveTermRecurrence.a`
- Truth anchor: `D5/S1/Recurrence/Algebraic/MatharA157100FiveTermRecurrence.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/MatharA157100FiveTermRecurrence.result`
- Dependency: [D5/S1/Recurrence/A308815DFiniteRecurrence](../A308815DFiniteRecurrence.md)
