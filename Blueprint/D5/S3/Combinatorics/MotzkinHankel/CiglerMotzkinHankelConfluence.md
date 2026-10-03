# Integral Confluence of Formal Alternants

## Abstract

The first possible coefficient of a rescaled alternant is a Vandermonde determinant times a coefficient determinant.

**Theorem 1.1 (The first alternant coefficient).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelConfluence.alternant_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelConfluence.alternant_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

Let R be any commutative ring, let m be a nonnegative integer, let f_i(y) be m formal power series over R, and let c_j be m elements of R, with indices starting at zero. Form the matrix with entry f_i(c_j y). Every coefficient of its determinant at an index below binom(m,2) is zero. The coefficient at index binom(m,2) equals the determinant of the Vandermonde matrix with entry c_i^j times the determinant of the matrix with entry the coefficient of y^j in f_i(y). The formula imposes no distinctness condition on the c_j and requires no division by factorials or differences of parameters.

## References

- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelConfluence.alternant_coefficients`
- Dependency: [D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelBranches](CiglerMotzkinHankelBranches.md)
