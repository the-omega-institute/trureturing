# The coefficient positivity clause is false

## Abstract

Refutation of reciprocal Gamma coefficient positivity.

**Theorem 1.1 (An admissible sequence with a negative coefficient).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReciprocalGammaTuran/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/kalmykov-karp-2013-reciprocal-gamma-turanian-coefficients` (refuted) by `D5/S3/Analytic/ReciprocalGammaTuran/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kalmykov-karp-2013-reciprocal-gamma-turanian-coefficients","declaration_gid":"D5/S3/Analytic/ReciprocalGammaTuran/Result.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

The constant unit sequence is nontrivial, nonnegative, log concave and has no internal zeros. The interior existence theorem supplies admissible parameters with a strictly negative second coefficient. Universal positivity at degree two would give the opposite strict inequality. This refutes the coefficient assertion while leaving the assertion concerning log concavity in the positive parameter range untouched.

## References

- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Result.result`
- Dependency: [D5/S3/Analytic/ReciprocalGammaTuran/Interior](Interior.md)
