# Integral column factorization and low-rank corrections

## Abstract

Integral column factorization and low-rank corrections

**Theorem 1.1 (A full minor generates the column module).**

Lean statement: `D5/S3/Zeros/GRH/New/Core/CappedMinorWitness.exists_maximal_minor_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Core/CappedMinorWitness.exists_maximal_minor_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over a valuation domain, a matrix with a nonzero full column minor admits an integral factorization through one selected full minor. The universal determinant divisibility applies to each Cramer numerator. Cancelling the nonzero determinant gives the integral coordinates of all columns.

**Theorem 1.2 (A capped full minor from a low-rank correction).**

Lean statement: `D5/S3/Zeros/GRH/New/Core/CappedMinorWitness.exists_capped_minor_dvd_of_low_rank_correction`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Core/CappedMinorWitness.exists_capped_minor_dvd_of_low_rank_correction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose that A times X plus B times C equals a times a square matrix with unit determinant. If B has r columns and A has c rows and columns, a nonzero full minor of the horizontal concatenation of A and z times the identity has determinant dividing a to the power c times z to the power r. Here z is nonzero. A triangular block elimination computes the corresponding determinant, and the integral factorization of the concatenation exhibits the selected determinant as a divisor.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Core/CappedMinorWitness.exists_capped_minor_dvd_of_low_rank_correction`
- Truth anchor: `D5/S3/Zeros/GRH/New/Core/CappedMinorWitness.exists_maximal_minor_factorization`
- Dependency: [D5/S3/Zeros/GRH/New/Core/MaximalMinors](MaximalMinors.md)
