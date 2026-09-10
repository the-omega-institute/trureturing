# Polynomial Tangent Descent

## Abstract

A polynomial with gradient parallel to a fixed nonzero vector depends on one linear form.

**Theorem 1.1 (Dependence on a linear form).**

$$\forall K, sigma: Type, \operatorname{Field}\left(K\right), \operatorname{CharZero}\left(K\right), \operatorname{Fintype}\left(sigma\right), c: sigma \to K, c \neq 0, p: \operatorname{MvPolynomial}\left(sigma, K\right),\ (\forall i, j \in sigma, c(j) \cdot \operatorname{pderiv}\left(i, p\right) = c(i) \cdot \operatorname{pderiv}\left(j, p\right)) \iff (\exists F: \operatorname{Polynomial}\left(K\right), p = \operatorname{aeval}\left(\sum_{i} c(i) \cdot X_{i}, F\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PolynomialTangentDescent.tangent_descent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be a field of characteristic zero, sigma a finite set of variables, c a nonzero K-valued function on sigma, and p a polynomial over K in those variables. Write ell for the sum of c(i) times X(i). The partial derivatives of p satisfy c(j) times partial_i p equals c(i) times partial_j p for every i and j if and only if p equals F(ell) for some univariate polynomial F over K. Products by c(i) denote scalar actions.

Choose j with c(j) nonzero. Replace X(j) by the inverse of c(j) times the difference between X(j) and the sum of c(i)X(i) over i different from j, and fix the other variables. The inverse substitution replaces X(j) by ell. The product rule, applied inductively to a polynomial, shows that each nonpivot partial derivative after substitution is the substitution of partial_i p minus c(i)/c(j) times partial_j p. The assumed identities make all these derivatives zero.

If a monomial contains a nonpivot variable with positive exponent, its coefficient contributes to a unique coefficient of that partial derivative, multiplied by the exponent. Characteristic zero makes this multiplier nonzero. Consequently no such monomial has a nonzero coefficient. The substituted polynomial is therefore F(X(j)), and applying the inverse substitution gives p = F(ell). Conversely the univariate chain rule gives partial_i F(ell) = c(i) F'(ell), which implies the stated identities.

The polynomial p may be zero or constant, and individual coefficients c(i) may vanish. No order or positivity is required. A nonzero c already ensures that a pivot exists, so no separate assumption that sigma is nonempty is needed.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/PolynomialTangentDescent.tangent_descent`
