# Coefficients and admissible sequences

## Abstract

Reciprocal Gamma series and coefficient positivity.

**Definition 1.1 (Reciprocal Gamma).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Defs.rgamma`

*Formalization.* `D5/S3/Analytic/ReciprocalGammaTuran/Defs.rgamma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real x, rgamma(x) is the inverse of the real Gamma value. It is zero at every nonpositive integer.

**Definition 1.2 (Admissible coefficient sequences).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Defs.AdmissibleSeq`

*Formalization.* `D5/S3/Analytic/ReciprocalGammaTuran/Defs.AdmissibleSeq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A sequence g from the natural numbers to the reals is admissible when it is nonzero at some index, nonnegative at every index, satisfies g(n-1)g(n+1) at most g(n) squared for every n at least one, and has no internal zeros: if a<b<c and g(a) and g(c) are nonzero, then g(b) is nonzero.

**Definition 1.3 (The finite Cauchy coefficient).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Defs.turanCoeff`

*Formalization.* `D5/S3/Analytic/ReciprocalGammaTuran/Defs.turanCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real sequence g, real parameters mu, alpha and beta, and natural m, sum over k from zero to m the product g(k)g(m-k) times the difference rgamma(k+mu+alpha)rgamma(m-k+mu+beta) minus rgamma(k+mu)rgamma(m-k+mu+alpha+beta).

**Definition 1.4 (Universal coefficient positivity).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Defs.claim`

*Formalization.* `D5/S3/Analytic/ReciprocalGammaTuran/Defs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every admissible sequence g and every real mu, alpha and beta with alpha and beta positive, mu at least minus one, and mu+alpha and mu+beta nonnegative, the Turanian coefficient is positive at every natural degree m.

**Theorem 1.5 (Values at the poles).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Defs.rgamma_neg_nat`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReciprocalGammaTuran/Defs.rgamma_neg_nat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, rgamma(-n) is zero. This follows directly from the real Gamma convention at nonpositive integers.

**Theorem 1.6 (The constant unit sequence).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Defs.admissible_one`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReciprocalGammaTuran/Defs.admissible_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sequence with value one at every natural index satisfies all four admissibility conditions.

## References

- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Defs.AdmissibleSeq`
- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Defs.admissible_one`
- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Defs.claim`
- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Defs.rgamma`
- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Defs.rgamma_neg_nat`
- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Defs.turanCoeff`
