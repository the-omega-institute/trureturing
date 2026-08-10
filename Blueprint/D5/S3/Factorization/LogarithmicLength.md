# Logarithmic Length from Prime Factorization

## Abstract

A natural number's logarithm is the exponent-weighted sum of its prime-factor logarithms.

**Definition 1.1 (Prime exponents define logarithmic length).**

$$\operatorname{factorizationLogLength}(n)=\sum_{p}\operatorname{factorization}(n)(p) \operatorname{log}(p)$$

*Formalization.* `D5/S3/Factorization/LogarithmicLength.factorizationLogLength` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The logarithmic length of a natural number is the finite sum over its prime-factorization support, weighting the logarithm of each prime by that prime's exponent.

**Theorem 1.2 (Prime-factor length equals the natural logarithm).**

$$\forall n\in \mathbb{N},\ \operatorname{factorizationLogLength}(n)=\operatorname{log}(n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/LogarithmicLength.factorization_log_length_eq_log` (`✓ std3`). ∎

*Citation.* Tom M. Apostol (1976). *Introduction to Analytic Number Theory*. DOI: [10.1007/978-1-4757-5579-4](https://doi.org/10.1007/978-1-4757-5579-4).

*Commentary.*

For every natural number, the additive length read from its prime exponents equals its real logarithm. For positive inputs this is the logarithm of the unique prime-power product; the zero input is included using the pinned library's conventions for the logarithm and factorization at zero. The identity is the exact bridge from multiplicative factorization coordinates to an additive real-valued readout asserted by the source atom.

The library was searched before proving. Pinned mathlib already contains the complete identity as Real.log_nat_eq_sum_factorization, supported internally by Finsupp.log_prod and Nat.prod_factorization_pow_eq_self. The Lean theorem is therefore a declared thin honest wrapper that only reverses the upstream equality to place the defined length on the left; no independent proof or stronger uniqueness claim is presented. The source atom contains no numerical certificate.

## References

- Truth anchor: `D5/S3/Factorization/LogarithmicLength.factorizationLogLength`
- Truth anchor: `D5/S3/Factorization/LogarithmicLength.factorization_log_length_eq_log`
