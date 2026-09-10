# Divisor Parity and Reflection

## Abstract

Prime-factor parity determines the commutation sign of divisor reflection.

**Theorem 1.1 (Divisor-operator commutation sign).**

$$\Gamma R=(-1)^{\operatorname{cardFactors}(N)}R\Gamma$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ExponentExchange/DivisorParity.factor_parity_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let N be a nonzero natural number. On the complex coefficient space of its divisors, Gamma multiplies the d coefficient by the sign of its prime-factor count, with multiplicity. R precomposes coefficients with d mapped to N/d; this involution sends the d basis vector to the N/d basis vector. The repository operator interface applies Mathlib's cardFactors_mul and normalizes the resulting powers of minus one.

## References

- Truth anchor: `D5/S3/Arith/ExponentExchange/DivisorParity.factor_parity_reflection`
