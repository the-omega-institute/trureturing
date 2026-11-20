# Real and imaginary coefficients of multivariate polynomials

## Abstract

Real and imaginary coefficient projections commute with evaluation on real inputs.

**Theorem 1.1 (Evaluation of the coefficient projections).**

Lean statement: `D5/S3/Quantum/Algebra/Polynomials/ComplexPolynomialCoefficients.coefficient_eval`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Polynomials/ComplexPolynomialCoefficients.coefficient_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking real and imaginary parts coefficientwise gives two real polynomials. After extending the coefficients to the complex numbers, their sum with the imaginary projection multiplied by the imaginary unit recovers the original polynomial. At real inputs the two projections evaluate to the real and imaginary parts of the original evaluation.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/Polynomials/ComplexPolynomialCoefficients.coefficient_eval`
