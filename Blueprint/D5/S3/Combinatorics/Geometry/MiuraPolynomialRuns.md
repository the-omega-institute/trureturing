# Rational weights for simultaneous positive run lengths

## Abstract

Rational weights for simultaneous positive run lengths.

**Definition 1.1 (One shifted falling product).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraPolynomialRuns.falling`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraPolynomialRuns.falling` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In either dimension variable, multiply k successive linear factors shifted by the occupied-axis count plus one.

**Definition 1.2 (A rational binomial weight).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraPolynomialRuns.runPolynomial`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraPolynomialRuns.runPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Divide the shifted falling product of length r-1 by the factorial of r-1.

**Definition 1.3 (Both axes in one polynomial).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraPolynomialRuns.jointRunPolynomial`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraPolynomialRuns.jointRunPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply the row weight in the first variable by the column weight in the second variable.

**Theorem 1.4 (Exact positive-vector cardinality).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraPolynomialRuns.joint_run_polynomial_eval`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraPolynomialRuns.joint_run_polynomial_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive run counts r,s and dimensions satisfying u+r at most m and v+s at most n, evaluating the polynomial at m,n equals the cardinality of the actual Cartesian product of positive row-run vectors of total m-u and positive column-run vectors of total n-v. The falling-factorial evaluation is the rational binomial identity. This statement counts positive vectors; identifying these vectors with a fiber of height functions requires a separate bijection.

**Theorem 1.5 (The degree is bounded by both run exponents).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraPolynomialRuns.joint_run_polynomial_degree_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraPolynomialRuns.joint_run_polynomial_degree_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive r,s, the total degree is at most r+s-2. Each axis supplies r-1 or s-1 linear factors, and multiplication adds these bounds.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraPolynomialRuns.falling`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraPolynomialRuns.jointRunPolynomial`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraPolynomialRuns.joint_run_polynomial_degree_le`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraPolynomialRuns.joint_run_polynomial_eval`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraPolynomialRuns.runPolynomial`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraRunCompositions](MiuraRunCompositions.md)
