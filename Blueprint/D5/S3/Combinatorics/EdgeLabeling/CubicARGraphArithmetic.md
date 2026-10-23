# Counting additive triples for cubic AR labeling

## Abstract

The additive-triple cardinality and the strict cubic-labeling union bound.

**Definition 1.1 (The free additive triples).**

Lean statement: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphArithmetic.additivePairs`

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphArithmetic.additivePairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite set contains the smaller ordered pair of labels in a triple a<b<a+b with all labels in the interval from three to m. It is formed as disjoint rows indexed by a minus three.

**Theorem 1.2 (The additive-triple constraints).**

Lean statement: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphArithmetic.mem_additivePairs`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphArithmetic.mem_additivePairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m at least six, membership of the pair (a,b) is equivalent to three at most a, a less than b, and a+b at most m.

**Theorem 1.3 (A square upper bound).**

Lean statement: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphArithmetic.four_mul_card_additivePairs_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphArithmetic.four_mul_card_additivePairs_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Four times the number of additive pairs is at most the square of m-5. This follows from the rectangular cardinality and the nonnegative square of the difference between its side lengths.

**Theorem 1.4 (The factorial-weighted strict union bound).**

Lean statement: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphArithmetic.bad_count_lt_factorial`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphArithmetic.bad_count_lt_factorial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m at least twelve, 3n=2m, and 4t at most (m-5)^2, the sum of (m-3)!, 2(2m-7)(m-4)!, and 6(n-3)t(m-5)! is strictly below (m-2)!. Multiply the normalized inequality by the positive factorial (m-5)! and use the factorial recurrence.

## References

- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphArithmetic.additivePairs`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphArithmetic.bad_count_lt_factorial`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphArithmetic.four_mul_card_additivePairs_le`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphArithmetic.mem_additivePairs`
