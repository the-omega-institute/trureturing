# Positive and increasing coefficients of actual formal exponentials

## Abstract

Positive and increasing coefficients of actual formal exponentials

The input g has rational values and only its positive indices occur. All coefficients are extracted from the literal formal exponential. The recurrence comes from its actual differential equation, rather than a recursive definition of a desired coefficient sequence.

**Theorem 1.1 (coefficient recurrence).**

Lean statement: `D5/S1/Recurrence/Witt/EulerExponentialCoefficients.coefficient_recurrence`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Witt/EulerExponentialCoefficients.coefficient_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coefficient extraction from X times the derivative gives the sum over k=0,...,n-1 with input g(k+1). At n=0 the two sides vanish.

**Theorem 1.2 (coefficient positive).**

Lean statement: `D5/S1/Recurrence/Witt/EulerExponentialCoefficients.coefficient_positive`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Witt/EulerExponentialCoefficients.coefficient_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strong induction applies the positive-index recurrence. Each summand is nonnegative, and the summand with residual degree zero is strictly positive. The constant coefficient is one.

**Theorem 1.3 (coefficient monotone).**

Lean statement: `D5/S1/Recurrence/Witt/EulerExponentialCoefficients.coefficient_monotone`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Witt/EulerExponentialCoefficients.coefficient_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compare the convolution equations at n and n+1. Their difference is controlled by g(1)-1 and the adjacent positive-index ghost differences, multiplied by already positive coefficients. This proves monotonicity on all natural degrees.

## References

- Truth anchor: `D5/S1/Recurrence/Witt/EulerExponentialCoefficients.coefficient_monotone`
- Truth anchor: `D5/S1/Recurrence/Witt/EulerExponentialCoefficients.coefficient_positive`
- Truth anchor: `D5/S1/Recurrence/Witt/EulerExponentialCoefficients.coefficient_recurrence`
- Dependency: [D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality](HannaDiagonalGhostPowerIntegrality.md)
