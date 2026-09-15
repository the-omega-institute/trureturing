# The Trinomial Odd Diagonal of OEIS A077864

## Abstract

Schulte's conjectured odd diagonal equals the coefficients of a rational power series.

OEIS A077864 is the expansion of (1-x)^(-1)/(1-x-2*x^2-x^3). Its FORMULA section records Deléham's order-four recurrence and Schulte's conjecture identifying its coefficients with an odd diagonal of the trinomial triangle A027907.

All indices are natural numbers. The trinomial value is the coefficient of X^r in (1+X+X^2)^m. The diagonal sum uses n/2 as integer division. The power series and its coefficient function take values in the rationals; coeff extracts a degree and inv denotes a power-series inverse. The operator expand 2 selects even powers and rescale(-1) reverses the sign of odd coefficients.

**Definition 1.1 (The trinomial coefficient).**

$$\forall m \in \mathbb{N}, \forall r \in \mathbb{N}, \operatorname{trinomial}\left(m, r\right) = \operatorname{coeff}\left((1 + X + (X)^{2})^{m}, r\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/TrinomialOddDiagonalRationalSeries.trinomial` (`✓ std3`).

*Citation.* Werner Schulte (2015). *OEIS A077864, Expansion of (1-x)^(-1)/(1-x-2*x^2-x^3)*. URL: <https://oeis.org/A077864>.

*Commentary.*

This is the coefficient definition of the rows of A027907.

**Definition 1.2 (The rational generating series).**

$$\operatorname{generatingSeries} = \operatorname{inv}\left((1 - X)\right) \cdot \operatorname{inv}\left((1 - X - 2 \cdot (X)^{2} - (X)^{3})\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/TrinomialOddDiagonalRationalSeries.generatingSeries` (`✓ std3`).

*Citation.* Werner Schulte (2015). *OEIS A077864, Expansion of (1-x)^(-1)/(1-x-2*x^2-x^3)*. URL: <https://oeis.org/A077864>.

*Commentary.*

This rational power series is the expansion named in A077864, with coefficients in the rationals.

**Definition 1.3 (The coefficient sequence).**

$$\forall n \in \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{generatingSeries}\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/TrinomialOddDiagonalRationalSeries.a` (`✓ std3`).

*Citation.* Werner Schulte (2015). *OEIS A077864, Expansion of (1-x)^(-1)/(1-x-2*x^2-x^3)*. URL: <https://oeis.org/A077864>.

*Commentary.*

The value a(n) is the degree-n coefficient of the rational generating series, so it is rational-valued in this formalization.

**Theorem 1.4 (The odd coefficient identity).**

$$\forall n \in \mathbb{N}, \operatorname{coeff}\left(2 \cdot n + 3, \operatorname{inv}\left((1 - (X)^{2} \cdot (1 + X + (X)^{2}))\right)\right) = \sum_{j \in \operatorname{range}\left(\operatorname{div}\left(n, 2\right) + 1\right)} (\operatorname{trinomial}\left(n + 1 - j, 2 \cdot j + 1\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/TrinomialOddDiagonalRationalSeries.odd_trinomial_diagonal_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substituted geometric powers have finite support at every fixed degree. Reflection of the finite sum and the polynomial degree tail bound give the displayed odd diagonal coefficient identity.

**Theorem 1.5 (Schulte's A077864 conjecture).**

$$\forall n \in \mathbb{N}, \operatorname{a}\left(n\right) = \sum_{j \in \operatorname{range}\left(\operatorname{div}\left(n, 2\right) + 1\right)} (\operatorname{trinomial}\left(n + 1 - j, 2 \cdot j + 1\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/TrinomialOddDiagonalRationalSeries.schulte_a077864` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a077864-trinomial-odd-diagonal-rational-series` (proved) by `D5/S1/Recurrence/Invariants/TrinomialOddDiagonalRationalSeries.schulte_a077864`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a077864-trinomial-odd-diagonal-rational-series","declaration_gid":"D5/S1/Recurrence/Invariants/TrinomialOddDiagonalRationalSeries.schulte_a077864","resolution_kind":"proved"} -->

*Citation.* Werner Schulte (2015). *OEIS A077864, Expansion of (1-x)^(-1)/(1-x-2*x^2-x^3)*. URL: <https://oeis.org/A077864>.

*Commentary.*

The two reflected inverse equations and their denominator product give the odd-part identity 2·X^3·(expand 2 G') = G - rescale(-1) G. Coefficient extraction reduces it to the preceding odd diagonal identity.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/TrinomialOddDiagonalRationalSeries.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/TrinomialOddDiagonalRationalSeries.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/TrinomialOddDiagonalRationalSeries.odd_trinomial_diagonal_coeff`
- Truth anchor: `D5/S1/Recurrence/Invariants/TrinomialOddDiagonalRationalSeries.schulte_a077864`
- Truth anchor: `D5/S1/Recurrence/Invariants/TrinomialOddDiagonalRationalSeries.trinomial`
