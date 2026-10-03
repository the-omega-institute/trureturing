# Formal Reciprocal Branches and Polynomial Exponents

## Abstract

Distinct reciprocal roots give two formal branches, and coefficients of integral unit powers are polynomial in the exponent.

**Theorem 1.1 (The two reciprocal formal branches).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelBranches.formal_branches`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelBranches.formal_branches` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

Let K be a field, let phi be a ring homomorphism from the integer polynomial ring in t and s to K, and let alpha be nonzero with alpha - alpha inverse nonzero and phi(t) = alpha + alpha inverse. There is a formal power series z(y) with constant coefficient alpha and z + z inverse = phi(t) - y. The constant coefficient of z - z inverse is nonzero. Among series with constant coefficient alpha, z is the unique solution of w squared - (phi(t) - y)w + 1 = 0. Put a = (phi(s) - y - z inverse)/(z - z inverse) and b = (z - phi(s) + y)/(z - z inverse). For every nonnegative integer r, (-1)^r p_r(y) after applying phi to its coefficients equals a z^r + b(z inverse)^r, while (-1)^(r+1) b_r(y) after the same coefficient map equals a(z inverse)^(r+1) + b z^(r+1). All these identities are formal power series identities over K.

**Theorem 1.2 (Polynomial dependence on an integral exponent).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelBranches.unit_power_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelBranches.unit_power_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

Let K be a field of characteristic zero, let u be an invertible formal power series with constant coefficient one, let H be any formal power series over K, and let h be a nonnegative integer. There is a polynomial P over K of natural degree at most h such that, for every integer n, P evaluated at n equals the coefficient of y^h in H(y)u(y)^n. The statement includes negative exponents, interpreted using the inverse of u.

## References

- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelBranches.formal_branches`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelBranches.unit_power_coefficients`
- Dependency: [D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelNegative](CiglerMotzkinHankelNegative.md)
