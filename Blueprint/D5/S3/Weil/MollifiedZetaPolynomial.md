# Finite Möbius convolution for the zeta mollifier

## Abstract

Finite Möbius convolution for the zeta mollifier

**Theorem 1.1 (Separate the finite convolution and the truncation error).**

Lean statement: `D5/S3/Weil/MollifiedZetaPolynomial.integral_norm_mollifiedZeta_sub_one_sq_le`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/MollifiedZetaPolynomial.integral_norm_mollifiedZeta_sub_one_sq_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying the finite zeta sum by the Möbius polynomial cancels all nonconstant coefficients through the Möbius cutoff. Above that cutoff the divisor count bounds the convolution coefficients. The actual mollified second moment on a segment away from the pole is controlled by the convolution tail and the zeta truncation error.

## References

- Truth anchor: `D5/S3/Weil/MollifiedZetaPolynomial.integral_norm_mollifiedZeta_sub_one_sq_le`
- Dependency: [D5/S3/Arith/Divisors/DivisorSubpower](../Arith/Divisors/DivisorSubpower.md)
