# Column Denominator Modes and Fixed Roots

## Abstract

Reciprocal modes factor the column denominator, and primitive roots give the fixed Chebyshev nodes for mixed confluence.

**Theorem 1.1 (The reciprocal-mode factorization).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDenominator.mode_denominator`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDenominator.mode_denominator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

Let K be a field, let phi map the integer polynomial ring in t to K, and choose a nonzero alpha with phi(t) = alpha + alpha inverse. For nonnegative k and m put e = (-1)^binom(k+1,2). The image Q of the specified column denominator is the product, for j from zero through m, of (1 - e alpha^((k+1)(m-2j)) x^(k+1))^(1+j(m-j)), with signed integer exponents on alpha. Its degree is (k+1)(m+1+binom(m+1,3)), and its leading coefficient is nonzero. Pairing j with m-j gives the Lucas factors; when m is even the central factor occurs once.

**Theorem 1.2 (Fixed roots and remainder confluence).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDenominator.fixed_roots`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDenominator.fixed_roots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

Let K be a field of characteristic zero, let phi map the integer polynomial ring in t to K, and let zeta be a primitive root of unity of order 2(k+1). For i from zero to k minus one put q_i = zeta^(i+1) and r_i = phi(t) + q_i + q_i inverse. The r_i are distinct, q_i^(k+1) = (-1)^(i+1), and (q_i - q_i inverse)p_n(r_i) = q_i^(n+1) - (q_i inverse)^(n+1), where p_n is the orthogonal polynomial after specializing s to t and applying phi. Moreover p_k(y) is the product of y-r_i. For every nonnegative m, polynomials f_i(y) indexed by i below m+k, and scalars c_j indexed below m, form A(y) with columns f_i(c_j y) followed by f_i(r_j). The coefficient of y^binom(m,2) in det A is det Vandermonde(c) times det Vandermonde(r), times the product of r_i^m, times the coefficient determinant of the remainders of f_i modulo y^m p_k(y). Its column j consists of coefficients of y^j.

## References

- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDenominator.fixed_roots`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDenominator.mode_denominator`
- Dependency: [D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnBranches](CiglerMotzkinColumnBranches.md)
