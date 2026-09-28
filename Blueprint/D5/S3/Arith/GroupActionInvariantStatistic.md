# Group-Action Invariant Statistics

## Abstract

Finite group actions turn local symmetry into arithmetic conservation.

**Theorem 1.1 (Transposition invariance extends to every permutation).**

Lean statement: `D5/S3/Arith/GroupActionInvariantStatistic.swap_invariant_permutation_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GroupActionInvariantStatistic.swap_invariant_permutation_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The preserving permutations form a subgroup. Mathlib's finite generation theorem for transpositions puts every permutation in that subgroup, so a local swap law becomes a global relabeling law.

**Theorem 1.2 (A nonempty finite symmetric statistic is constant).**

Lean statement: `D5/S3/Arith/GroupActionInvariantStatistic.swap_invariant_is_constant`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GroupActionInvariantStatistic.swap_invariant_is_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The swap exchanging a chosen base point with any target point transports the target value back to the base value.

**Theorem 1.3 (Invariant orbit sums are cardinality multiples).**

Lean statement: `D5/S3/Arith/GroupActionInvariantStatistic.orbit_sum_eq_card_mul_value`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GroupActionInvariantStatistic.orbit_sum_eq_card_mul_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A natural statistic constant along a finite group orbit sums to the orbit cardinality multiplied by its value at the base point.

**Theorem 1.4 (Orbit sums satisfy a divisibility law).**

Lean statement: `D5/S3/Arith/GroupActionInvariantStatistic.orbit_sum_dvd_card`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GroupActionInvariantStatistic.orbit_sum_dvd_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The orbit cardinality divides every finite natural-valued invariant sum. Failure of this divisibility is a certificate against the proposed group symmetry.

**Theorem 1.5 (Finite transposition symmetry forces cardinal divisibility).**

Lean statement: `D5/S3/Arith/GroupActionInvariantStatistic.swap_invariant_sum_dvd_card`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GroupActionInvariantStatistic.swap_invariant_sum_dvd_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a nonempty finite carrier, the total of a transposition-invariant natural statistic is divisible by the carrier cardinality.

**Theorem 1.6 (Full symmetry on Fin n forces n-divisibility).**

Lean statement: `D5/S3/Arith/GroupActionInvariantStatistic.fin_sum_dvd_card`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GroupActionInvariantStatistic.fin_sum_dvd_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive n, a transposition-invariant natural statistic on Fin n has a total divisible by n. This is the concrete arithmetic interface for later residue and counting applications.

## References

- Truth anchor: `D5/S3/Arith/GroupActionInvariantStatistic.fin_sum_dvd_card`
- Truth anchor: `D5/S3/Arith/GroupActionInvariantStatistic.orbit_sum_dvd_card`
- Truth anchor: `D5/S3/Arith/GroupActionInvariantStatistic.orbit_sum_eq_card_mul_value`
- Truth anchor: `D5/S3/Arith/GroupActionInvariantStatistic.swap_invariant_is_constant`
- Truth anchor: `D5/S3/Arith/GroupActionInvariantStatistic.swap_invariant_permutation_invariant`
- Truth anchor: `D5/S3/Arith/GroupActionInvariantStatistic.swap_invariant_sum_dvd_card`
