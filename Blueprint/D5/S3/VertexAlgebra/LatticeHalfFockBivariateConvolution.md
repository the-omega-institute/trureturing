# Finite Coefficient Convolutions

## Abstract

Finite polynomial convolutions supply the coefficient shifts of native half-Fock products.

For any commutative ring Ring and arbitrary integer-indexed creation sequences, coefficientConvolution sums over the finite support of a univariate polynomial. bivariateCoefficientConvolution sums over the finite monomial support of an MvPolynomial (Fin 2) Ring, multiplying each coefficient by the two creation values at first+exponent(0) and second+exponent(1). These are Ring-linear maps. No support or convergence assumption on the creation sequences is required.

**Theorem 1.1 (A univariate monomial selects one creation coefficient).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockBivariateConvolution.coefficientConvolution_monomial`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockBivariateConvolution.coefficientConvolution_monomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural degree and coefficient in Ring, the monomial maps to coefficient * creation(shift+degree). The constant case is consumed by the oscillator constant calculation in OrderedProducts.

**Theorem 1.2 (The univariate convolution is its polynomial support sum).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockBivariateConvolution.coefficientConvolution_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockBivariateConvolution.coefficientConvolution_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every polynomial, coefficientConvolution equals the sum of polynomial.coeff(degree) * creation(shift+degree) over polynomial.support. OrderedProducts uses this identity to identify the actual oscillator coefficient.

**Theorem 1.3 (A bivariate monomial selects two creation coefficients).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockBivariateConvolution.bivariateCoefficientConvolution_monomial`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockBivariateConvolution.bivariateCoefficientConvolution_monomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A monomial with exponent : Fin 2 to finite-support N maps to coefficient * (left(first+exponent(0)) * right(second+exponent(1))). ProductKernel specializes this to the two half-creation sequences.

**Theorem 1.4 (A constant polynomial factor leaves the convolution).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockBivariateConvolution.bivariateCoefficientConvolution_C_mul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockBivariateConvolution.bivariateCoefficientConvolution_C_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication of the input polynomial by C coefficient multiplies the output by coefficient. ProductKernel consumes this linearity specialization in its creator recurrence; it is an algebraic helper.

**Theorem 1.5 (The first variable shifts the first creation index).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockBivariateConvolution.bivariateCoefficientConvolution_X_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockBivariateConvolution.bivariateCoefficientConvolution_X_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural degree, multiplying by X 0 ^ degree changes first to first+degree and leaves second fixed. Polynomial induction proves the identity for arbitrary input polynomials.

**Theorem 1.6 (The second variable shifts the second creation index).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockBivariateConvolution.bivariateCoefficientConvolution_X_one`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockBivariateConvolution.bivariateCoefficientConvolution_X_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural degree, multiplying by X 1 ^ degree changes second to second+degree and leaves first fixed. Together the two shift laws supply the independent oscillator shifts in ProductKernel.

These repository-derived finite polynomial identities reuse the existing Finsupp linear-sum and polynomial coefficient interfaces. Their declarations are owned by this module in the LatticeActualProductKernel namespace. Finiteness here belongs to each input polynomial; it gives no finite bivariate or endomorphism support for an entire field and establishes no analytic convergence or locality by itself.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockBivariateConvolution.bivariateCoefficientConvolution_C_mul`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockBivariateConvolution.bivariateCoefficientConvolution_X_one`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockBivariateConvolution.bivariateCoefficientConvolution_X_zero`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockBivariateConvolution.bivariateCoefficientConvolution_monomial`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockBivariateConvolution.coefficientConvolution_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockBivariateConvolution.coefficientConvolution_monomial`
- Dependency: [D5/S3/VertexAlgebra/LatticeActualProductKernel](LatticeActualProductKernel.md)
