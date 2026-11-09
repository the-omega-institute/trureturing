# Reuse-only weighted Mangoldt suppliers

## Abstract

Retained arithmetic suppliers consumed by the full actual-K source attempt.

**Theorem 1.1 (Complete Chebyshev tail bound).**

Lean statement: `D5/S3/Weil/Mertens/WeightedMangoldtRate.chebyshev_tail_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/WeightedMangoldtRate.chebyshev_tail_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive c, nonnegative D, X>=2 and x>=X, an actual psi error bound D u exp(-2c(log u)^(1/10)) bounds the complete tail integral by D times the full positive weight mass times exp(-c(log x)^(1/10)). The retained proof body is unchanged. This visibility export is consumed to obtain the exact original B in the full certificate; it is not a standalone content request.

**Theorem 1.2 (Retained inclusive Mangoldt rate).**

Lean statement: `D5/S3/Weil/Mertens/WeightedMangoldtRate.E1Lambda_stretched_exponential`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/WeightedMangoldtRate.E1Lambda_stretched_exponential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The retained unconditional theorem gives positive c,C and X>=2 with abs(E1Lambda(x)+gamma)<=C exp(-c(log x)^(1/10)) for every x>=X. It includes every prime power and equality at cutoffs. Its earlier evidence remains separately scoped. This payload reuses its arithmetic suppliers and does not seek standalone readmission of this theorem or claim a new compilation.

## References

- Truth anchor: `D5/S3/Weil/Mertens/WeightedMangoldtRate.E1Lambda_stretched_exponential`
- Truth anchor: `D5/S3/Weil/Mertens/WeightedMangoldtRate.chebyshev_tail_bound`
- Dependency: [D5/S3/Weil/Mertens/WeightedPrimeLimit](WeightedPrimeLimit.md)
