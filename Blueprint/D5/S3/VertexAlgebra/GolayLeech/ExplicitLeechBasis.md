# Exact integral construction

## Abstract

Explicit Golay-congruence lattice mathematics.

**Theorem 1.1 (Literal basis columns).**

Lean statement: `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechBasis.finite_column_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechBasis.finite_column_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each of the twenty-four integer columns has a supplied explicit binary message and the required parity and sum congruences. All column identities are kernel checked.

**Theorem 1.2 (Integer generator coordinates).**

Lean statement: `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechBasis.finite_generator_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechBasis.finite_generator_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sixty original generators are eight times each unit coordinate, twenty-three four-times differences, twice each polynomial generator and the odd vector (-3,1,...,1). Literal integer coordinates in the supplied basis are checked by matrix multiplication.

**Theorem 1.3 (Integral Gram identity).**

Lean statement: `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechBasis.finite_gram_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechBasis.finite_gram_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal Gram matrix satisfies B-transpose times B equals eight times G. Symmetry and even diagonal are checked entrywise.

**Theorem 1.4 (Unit Gram determinant).**

Lean statement: `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechBasis.gram_determinant`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechBasis.gram_determinant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The triangular integer basis has determinant two to the thirty-sixth power. Taking determinants in the exact scaled Gram identity proves determinant G equals one; no positive or unimodular matrix is assumed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechBasis.finite_column_certificate`
- Truth anchor: `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechBasis.finite_generator_coordinates`
- Truth anchor: `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechBasis.finite_gram_certificate`
- Truth anchor: `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechBasis.gram_determinant`
- Dependency: [D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechCongruence](ExplicitLeechCongruence.md)
