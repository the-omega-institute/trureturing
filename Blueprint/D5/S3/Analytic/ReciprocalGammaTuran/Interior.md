# Interior coefficients

## Abstract

Negative reciprocal Gamma Turanian coefficients.

**Theorem 1.1 (Continuity in all parameters).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Interior.continuous_turanCoeff_two`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReciprocalGammaTuran/Interior.continuous_turanCoeff_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second coefficient for the constant unit sequence is jointly continuous in mu, alpha and beta on the whole real parameter space. The inverse complex Gamma function is entire. Restriction to the real axis gives continuity even at its zeros, and finite sums and products preserve continuity.

**Theorem 1.2 (Strictly interior violations).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Interior.interior_failure`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReciprocalGammaTuran/Interior.interior_failure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exist positive alpha and beta and mu at least minus one such that mu+alpha and mu+beta are strictly positive and the second coefficient is strictly negative. Continuity preserves the boundary negativity when mu is increased by a sufficiently small positive amount.

## References

- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Interior.continuous_turanCoeff_two`
- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Interior.interior_failure`
- Dependency: [D5/S3/Analytic/ReciprocalGammaTuran/Boundary](Boundary.md)
