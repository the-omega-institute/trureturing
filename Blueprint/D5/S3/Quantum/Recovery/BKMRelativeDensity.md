# Relative order of the finite BKM coefficient

## Abstract

The actual BKM integral and its order under a relative density sandwich.

**Definition 1.1 (BKM power integral).**

Lean statement: `D5/S3/Quantum/Recovery/BKMRelativeDensity.omega`

*Formalization.* `D5/S3/Quantum/Recovery/BKMRelativeDensity.omega` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Integrate a^t X a^(1−t) for t between zero and one using the real spectral powers of a.

**Definition 1.2 (Coefficient of the power integrand).**

Lean statement: `D5/S3/Quantum/Recovery/BKMRelativeDensity.powerCoefficient`

*Formalization.* `D5/S3/Quantum/Recovery/BKMRelativeDensity.powerCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In column vectorization the coefficient at t is the Kronecker product of the transpose of a^(1−t) with a^t.

**Definition 1.3 (BKM coefficient).**

Lean statement: `D5/S3/Quantum/Recovery/BKMRelativeDensity.omegaCoefficient`

*Formalization.* `D5/S3/Quantum/Recovery/BKMRelativeDensity.omegaCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient is the Bochner integral of the power coefficients from zero to one.

**Theorem 1.4 (Action of the integrated coefficient).**

Lean statement: `D5/S3/Quantum/Recovery/BKMRelativeDensity.omegaCoefficient_mulVec`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMRelativeDensity.omegaCoefficient_mulVec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite a, multiplication by the coefficient on vec X gives vec (omega a X). The two linear maps commute with the integral.

**Theorem 1.5 (Relative Loewner bounds).**

Lean statement: `D5/S3/Quantum/Recovery/BKMRelativeDensity.omegaCoefficient_relative_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMRelativeDensity.omegaCoefficient_relative_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite a and b with 0 < ℓ ≤ u and ℓb ≤ a ≤ ub, the BKM coefficients obey the same sandwich. Fractional-power monotonicity bounds both factors of the Kronecker product. The complementary exponents recover the original constants before integration.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/BKMRelativeDensity.omega`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMRelativeDensity.omegaCoefficient`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMRelativeDensity.omegaCoefficient_mulVec`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMRelativeDensity.omegaCoefficient_relative_bounds`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMRelativeDensity.powerCoefficient`
- Dependency: [D5/S3/Quantum/Matrix/SpectralPower](../Matrix/SpectralPower.md)
