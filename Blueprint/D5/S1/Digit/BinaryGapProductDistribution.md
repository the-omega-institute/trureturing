# Binary Gap Product Distribution

## Abstract

Binary gap products are counted by ordered nonunit gaps and unit-gap insertions.

**Definition 1.1 (The product of successive binary gaps).**

Lean statement: `D5/S1/Digit/BinaryGapProductDistribution.gapProduct`

*Formalization.* `D5/S1/Digit/BinaryGapProductDistribution.gapProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Nat.bitIndices lists the set-bit positions in increasing order. Taking successive differences and multiplying them defines the gap product. The empty product is one, including for a number with a single set bit.

**Definition 1.2 (The distribution on a binary interval).**

Lean statement: `D5/S1/Digit/BinaryGapProductDistribution.gapProductCount`

*Formalization.* `D5/S1/Digit/BinaryGapProductDistribution.gapProductCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The count is the cardinality of the natural numbers in the half-open interval from two raised to n to two raised to (n + 1), filtered by gap product k. Thus n is precisely the top set-bit position.

**Theorem 1.3 (Successive differences undo cumulative positions).**

Lean statement: `D5/S1/Digit/BinaryGapProductDistribution.gaps_positions`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/BinaryGapProductDistribution.gaps_positions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Starting at a chosen lowest position and successively adding the gaps recovers a list whose successive differences are exactly those gaps.

**Theorem 1.4 (Cumulative gaps recover sorted positions).**

Lean statement: `D5/S1/Digit/BinaryGapProductDistribution.positions_gaps`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/BinaryGapProductDistribution.positions_gaps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonempty strictly increasing list, its first position and its successive differences reconstruct the entire list.

**Definition 1.5 (Bounded positive gaps are equivalent to binary integers).**

Lean statement: `D5/S1/Digit/BinaryGapProductDistribution.gapSequenceEquiv`

*Formalization.* `D5/S1/Digit/BinaryGapProductDistribution.gapSequenceEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A positive gap list with sum at most n determines its lowest set bit as n minus that sum. The forward map sums powers of two at the cumulative positions; the inverse takes gaps of Nat.bitIndices. Mathlib's bitIndices_sum_map_two_pow verifies the binary reconstruction, and finite geometric-sum bounds verify the interval endpoints.

**Theorem 1.6 (Transport the product filter through the binary bijection).**

Lean statement: `D5/S1/Digit/BinaryGapProductDistribution.gapProductCount_eq_gapSequences`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/BinaryGapProductDistribution.gapProductCount_eq_gapSequences` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original interval count equals the number of positive gap lists with sum at most n and product k. The proof uses explicit forward and inverse maps in Finset.card_bij.

**Theorem 1.7 (The finite index set contains exactly the required ordered tuples).**

Lean statement: `D5/S1/Digit/BinaryGapProductDistribution.mem_reducedTuples`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/BinaryGapProductDistribution.mem_reducedTuples` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Membership in reducedTuples is equivalent to every entry being at least two, the ordered list's product being k, and its sum being at most n. Lists retain order and repeated entries; there is no quotient by permutation. The empty list is included when k is one.

**Theorem 1.8 (Unit-run compression loses no information).**

Lean statement: `D5/S1/Digit/BinaryGapProductDistribution.insertUnits_splitUnits`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/BinaryGapProductDistribution.insertUnits_splitUnits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

splitUnits removes each unit gap and records the lengths of the unit runs before, between, and after the remaining entries. Reinsertion recovers the original gap list exactly.

**Theorem 1.9 (The reduced tuple and run counts are unique).**

Lean statement: `D5/S1/Digit/BinaryGapProductDistribution.splitUnits_insertUnits`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/BinaryGapProductDistribution.splitUnits_insertUnits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If none of the reduced entries equals one and the run-count list has one more entry than the reduced tuple, splitting after insertion returns both input lists. Together the two inverse lemmas give the explicit unit-gap insertion bijection.

**Theorem 1.10 (Bounded unit-run counts satisfy stars and bars).**

Lean statement: `D5/S1/Digit/BinaryGapProductDistribution.card_unitPlacements`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/BinaryGapProductDistribution.card_unitPlacements` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The number of nonnegative lists of a prescribed length with sum at most a given budget is the binomial coefficient choosing the length from budget plus length. Disjoint first-entry fibers reduce the proof to Mathlib's Nat.sum_range_add_choose.

**Theorem 1.11 (Each reduced tuple contributes its binomial weight).**

Lean statement: `D5/S1/Digit/BinaryGapProductDistribution.card_reduced_fiber`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/BinaryGapProductDistribution.card_reduced_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a reduced tuple of length r and sum s, its fiber consists of r plus one unit-run counts with total at most n minus s. The unused budget is exactly the lowest set-bit position. Its cardinality is the binomial coefficient choosing r plus one from n minus s plus r plus one.

**Theorem 1.12 (The binary gap-product distribution is the ordered-tuple sum).**

Lean statement: `D5/S1/Digit/BinaryGapProductDistribution.gapProductCount_eq_composition_sum`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/BinaryGapProductDistribution.gapProductCount_eq_composition_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sum the preceding fiber cardinalities over all ordered tuples whose entries are at least two, product is k, and sum is at most n. Finset.card_eq_sum_card_fiberwise partitions the bounded positive gap lists by their reduced tuple. The theorem holds for all natural n and k, and hence in particular for every positive k as requested in the general binary-gap question MO 469990.

**Theorem 1.13 (The empty tuple contributes n plus one).**

Lean statement: `D5/S1/Digit/BinaryGapProductDistribution.gapProductCount_one`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/BinaryGapProductDistribution.gapProductCount_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A reduced tuple with product one must be empty. Specializing the composition sum gives exactly n plus one numbers with gap product one. A separate kernel-decided sanity example checks that the count for n equal to four and k equal to two is six.

## References

- Truth anchor: `D5/S1/Digit/BinaryGapProductDistribution.card_reduced_fiber`
- Truth anchor: `D5/S1/Digit/BinaryGapProductDistribution.card_unitPlacements`
- Truth anchor: `D5/S1/Digit/BinaryGapProductDistribution.gapProduct`
- Truth anchor: `D5/S1/Digit/BinaryGapProductDistribution.gapProductCount`
- Truth anchor: `D5/S1/Digit/BinaryGapProductDistribution.gapProductCount_eq_composition_sum`
- Truth anchor: `D5/S1/Digit/BinaryGapProductDistribution.gapProductCount_eq_gapSequences`
- Truth anchor: `D5/S1/Digit/BinaryGapProductDistribution.gapProductCount_one`
- Truth anchor: `D5/S1/Digit/BinaryGapProductDistribution.gapSequenceEquiv`
- Truth anchor: `D5/S1/Digit/BinaryGapProductDistribution.gaps_positions`
- Truth anchor: `D5/S1/Digit/BinaryGapProductDistribution.insertUnits_splitUnits`
- Truth anchor: `D5/S1/Digit/BinaryGapProductDistribution.mem_reducedTuples`
- Truth anchor: `D5/S1/Digit/BinaryGapProductDistribution.positions_gaps`
- Truth anchor: `D5/S1/Digit/BinaryGapProductDistribution.splitUnits_insertUnits`
