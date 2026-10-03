# Remainder Determinants and Mixed Confluence

## Abstract

Monic division transforms modified moment determinants, and fixed columns preserve the confluence order of the varying columns.

**Theorem 1.1 (Monic multiplier determinants).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDeterminant.multiplier_remainders`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDeterminant.multiplier_remainders` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

Let R be a nontrivial commutative ring, let p_i be monic polynomials of degree i, and let ell be an R-linear functional with ell(p_i p_j) equal to one when i equals j and zero otherwise. For any monic polynomial g of degree h and any nonnegative n, the determinant of ell(g y^(i+j)) for indices i and j below n equals (-1)^(nh) times the h by h determinant whose entry in row i and column j is the coefficient of y^j in the remainder of p_{n+i} modulo g. Integral triangular changes of basis and monic division give the identity, including empty matrices.

**Theorem 1.2 (Confluence with fixed columns).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDeterminant.mixed_confluence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDeterminant.mixed_confluence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

Let R be a commutative ring and m and k be nonnegative integers. Choose formal series f_i(y) for rows i below m + k, scalars c_j for j below m, and fixed entries g_{i,j} for j below k. Form A(y) with first m columns f_i(c_j y) and last k columns g_{i,j}. Form J with first m columns the coefficients of y^j in f_i and the same last k columns. Every coefficient of det A below binom(m,2) vanishes, and its coefficient at binom(m,2) is det Vandermonde(c) times det J. Expansion along the fixed columns reduces the formula to alternant confluence.

## References

- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDeterminant.mixed_confluence`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDeterminant.multiplier_remainders`
- Dependency: [D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnTransfer](CiglerMotzkinColumnTransfer.md)
- Dependency: [D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelConfluence](CiglerMotzkinHankelConfluence.md)
