# Hankel Determinant Jacobi Coefficient

## Abstract

The determinant-defined Hankel Jacobi coefficient satisfies its squared ratio and is positive when three neighboring determinants are positive.

**Theorem 1.1 (The determinant-defined coefficient obeys the Hankel ratio).**

$$\begin{gathered}\forall m: \mathbb{N} \to \mathbb{R}, k \in \mathbb{N}_{>0},\\{}0 \leq \operatorname{hankelDet}\left(m, k - 1\right) \times \operatorname{hankelDet}\left(m, k + 1\right) \land \operatorname{hankelDet}\left(m, k\right) \neq 0 \Rightarrow \\{}\operatorname{hankelJacobiCoefficient}\left(m, k\right)^{2} = \frac{\operatorname{hankelDet}\left(m, k - 1\right) \times \operatorname{hankelDet}\left(m, k + 1\right)}{\operatorname{hankelDet}\left(m, k\right)^{2}}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Moments/HankelJacobiDeterminant.hankel_jacobi_coefficient_sq_eq_det_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a real moment sequence m, let the order-j determinant be that of the (j + 1)-square Hankel matrix with entry m(r + s). At every positive index k, a nonnegative product of the two neighboring determinants gives a real square root, while a nonzero current determinant permits division.

Under those hypotheses, squaring the determinant-defined coefficient gives the neighboring-determinant product divided by the square of the current determinant. This identifies only the value built from the square root and Hankel determinants; it does not assert that the value is a coefficient of an orthogonal-polynomial recurrence.

**Lemma 1.2 (Positive neighboring determinants give a positive coefficient).**

$$\begin{gathered}\forall m: \mathbb{N} \to \mathbb{R}, k \in \mathbb{N}_{>0},\\{}0 < \operatorname{hankelDet}\left(m, k - 1\right) \land 0 < \operatorname{hankelDet}\left(m, k\right) \land 0 < \operatorname{hankelDet}\left(m, k + 1\right) \Rightarrow \\{}0 < \operatorname{hankelJacobiCoefficient}\left(m, k\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Moments/HankelJacobiDeterminant.hankel_jacobi_coefficient_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the preceding, current, and following leading Hankel determinants are all positive, then the product under the square root is positive and its square root is positive. Dividing by the positive current determinant leaves the determinant-defined coefficient strictly positive.

These hypotheses also satisfy the nonnegativity and nonvanishing conditions of the squared identity. The extra sign information selects the positive value that is lost when only the square of the coefficient is retained.

## References

- Truth anchor: `D5/S3/Constants/Moments/HankelJacobiDeterminant.hankel_jacobi_coefficient_pos`
- Truth anchor: `D5/S3/Constants/Moments/HankelJacobiDeterminant.hankel_jacobi_coefficient_sq_eq_det_ratio`
