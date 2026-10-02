# Represented Spanning Polynomial Hessian Induction

## Abstract

Every represented reciprocal-factorial spanning polynomial satisfies the division-free reverse Hessian inequality at positive real coordinates.

The column field is arbitrary and the ambient vector space is finite-dimensional. The finite index set consists of physical columns: zero, repeated and scalar-parallel columns remain distinct. The real direction vector has unrestricted signs.

**Theorem 1.1 (Division-Free Reverse Hessian Bound).**

Lean statement: `D5/S3/Resource/SimplexCoverageInduction.spanningPolynomial_reverse`

*Proof.* Machine-checked in Lean as `D5/S3/Resource/SimplexCoverageInduction.spanningPolynomial_reverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural degree d, positive x, and real y, let f be the actual represented spanning polynomial, g its evaluated polynomial gradient, and H its evaluated polynomial Hessian. Then d f(x) y^T H y is at most (d-1)(g^T y)^2. No full-spanning or nonempty-index premise is required.

Induction generalizes the contracted subspace U. Degree two uses the quotient-rank bound. At higher degrees the actual derivative contractions and third-derivative Euler identity give the quadratic bootstrap. The normalized Hessian on derivative-positive coordinates has nonnegative entries, connected positive support and a strictly positive fixed vector. Its connected normalization bound gives nonpositivity on the gradient hyperplane; Euler square decomposition gives the unrestricted inequality.

Inactive derivative polynomials and their Hessian rows vanish by the rank obstruction. Their coordinates are transported back to the original index set rather than deleting physical columns. Empty indices, zero evaluation, and unspanned families are included. Degrees zero and one have zero Hessian.

The statement concerns algebraic polynomial derivatives. Analytic root concavity and a sampling or expected-time optimizer require additional bridges.

## References

- Truth anchor: `D5/S3/Resource/SimplexCoverageInduction.spanningPolynomial_reverse`
- Dependency: [D5/S3/Resource/SimplexCoveragePolynomial](SimplexCoveragePolynomial.md)
