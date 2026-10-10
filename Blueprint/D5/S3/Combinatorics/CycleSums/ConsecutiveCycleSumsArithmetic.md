# Triangular cores and interval subset sums

## Abstract

Arithmetic for consecutive cycle completion: triangular totals, interval subset sums and the least usable core.

**Definition 1.1 (Triangular total).**

Lean statement: `D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSumsArithmetic.tri`

*Formalization.* `D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSumsArithmetic.tri` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural number n, tri n is n times n plus one divided by two.

**Theorem 1.2 (Subset sums cover the core interval).**

Lean statement: `D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSumsArithmetic.subset_sums`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSumsArithmetic.subset_sums` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k at least four, every integer s between two and tri k minus three is the sum of a finite subset of the labels two through k. Induction adjoins k plus one to cover a second interval; the two intervals overlap or abut.

**Theorem 1.3 (A short core with a quadratic edge budget).**

Lean statement: `D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSumsArithmetic.choose_core`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSumsArithmetic.choose_core` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least eight there exists k at least four and less than n with tri k at least n plus four and the square of k minus one strictly less than twice n plus eight. Choose the least qualifying k; its predecessor triangular total is less than n plus four.

**Definition 1.4 (Tail-prefix total).**

Lean statement: `D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSumsArithmetic.tail`

*Formalization.* `D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSumsArithmetic.tail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The tail total from core endpoint k to endpoint j sums the labels k plus one through j.

**Theorem 1.5 (Tail translates cover every interior sum).**

Lean statement: `D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSumsArithmetic.interval_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSumsArithmetic.interval_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If k is at most n and tri k is at least n plus four, every q from three through tri n minus two belongs to an interval from three plus tail k j through tri k plus tail k j minus two for an endpoint j between k and n. Induction extends the endpoint; the next label is bounded by the core interval width, preventing gaps.

**Theorem 1.6 (Sum of all labels).**

Lean statement: `D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSumsArithmetic.sum_Icc_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSumsArithmetic.sum_Icc_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum of labels one through n is tri n.

**Theorem 1.7 (Sum excluding the hub label).**

Lean statement: `D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSumsArithmetic.sum_Icc_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSumsArithmetic.sum_Icc_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least one, the sum of labels two through n is tri n minus one.

## References

- Truth anchor: `D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSumsArithmetic.choose_core`
- Truth anchor: `D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSumsArithmetic.interval_cover`
- Truth anchor: `D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSumsArithmetic.subset_sums`
- Truth anchor: `D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSumsArithmetic.sum_Icc_one`
- Truth anchor: `D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSumsArithmetic.sum_Icc_two`
- Truth anchor: `D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSumsArithmetic.tail`
- Truth anchor: `D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSumsArithmetic.tri`
