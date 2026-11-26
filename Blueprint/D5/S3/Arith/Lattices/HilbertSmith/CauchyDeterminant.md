# The Cauchy determinant

## Abstract

The determinant of a matrix of reciprocals of pairwise sums factors into two ordered difference products.

**Theorem 1.1 (Cauchy determinant product).**

Lean statement: `D5/S3/Arith/Lattices/HilbertSmith/CauchyDeterminant.det_cauchyMatrix`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/HilbertSmith/CauchyDeterminant.det_cauchyMatrix` (`✓ std3`). ∎

*Citation.* Christian Krattenthaler (1999). *Advanced Determinant Calculus*. DOI: [10.48550/arXiv.math/9902004](https://doi.org/10.48550/arXiv.math/9902004). URL: <https://arxiv.org/abs/math/9902004>.

*Commentary.*

Let x and y be ordered arrays of the same finite length over a field. Suppose every sum x(i)+y(j) is nonzero. The determinant of the matrix with entries 1/(x(i)+y(j)) is the product of x(j)-x(i) over i<j times the product of y(j)-y(i) over i<j, divided by the product of x(i)+y(j) over all ordered row and column pairs. Empty products equal one, and repeated coordinates are allowed.

In positive dimension, eliminate the first column using its nonzero pivot. The remaining Schur complement is the smaller Cauchy matrix with each row and column scaled by its difference from the first coordinate divided by its sum with the first coordinate on the opposite side. Multiplying the scales, the pivot and the smaller determinant gives the products in the formula.

## References

- Truth anchor: `D5/S3/Arith/Lattices/HilbertSmith/CauchyDeterminant.det_cauchyMatrix`
