# Coefficient Newton Foundations

## Abstract

Partial Newton interface foundations: uniqueness, Vieta, and counted roots.

**Theorem 1.1 (Uniqueness of the coefficient recursion).**

Lean statement: `D5/S3/Constants/Moments/CoefficientNewtonSums.newton_sum_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Moments/CoefficientNewtonSums.newton_sum_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strong induction identifies any sequence satisfying the initial value and the Newton recurrence with the recursively defined sequence, over an arbitrary commutative ring. Identification with polynomial root sums and the Hermite parity block identity remain unproved.

**Theorem 1.2 (Vieta including the zero coefficient tail).**

Lean statement: `D5/S3/Constants/Moments/CoefficientNewtonSums.descending_coeff_eq_root_esymm`

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Moments/CoefficientNewtonSums.descending_coeff_eq_root_esymm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a monic polynomial of the stated degree, a root list whose multiset equals the polynomial roots determines every descending coefficient. The equality includes coefficients beyond the degree.

**Theorem 1.3 (Enumeration retains multiplicities).**

Lean statement: `D5/S3/Constants/Moments/CoefficientNewtonSums.exists_root_enumeration`

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Moments/CoefficientNewtonSums.exists_root_enumeration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The list is obtained from the polynomial root multiset, with length equal to the degree because complex polynomials split. No distinct-root set replaces the multiset. Complete Hermite and truncated Hankel matrices have separate structure types. No FFC positivity assertion is made.

## References

- Truth anchor: `D5/S3/Constants/Moments/CoefficientNewtonSums.descending_coeff_eq_root_esymm`
- Truth anchor: `D5/S3/Constants/Moments/CoefficientNewtonSums.exists_root_enumeration`
- Truth anchor: `D5/S3/Constants/Moments/CoefficientNewtonSums.newton_sum_unique`
