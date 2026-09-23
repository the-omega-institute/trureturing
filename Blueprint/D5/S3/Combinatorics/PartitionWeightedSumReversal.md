# Reversal and the Weighted Sum of a Partition

## Abstract

Reversing a partition leaves the divisibility of its weighted sum by the total unchanged, because the weighted sum of a list and of its reverse add to one more than the length times the total.

**Definition 1.1 (The one-based weighted sum).**

$$W(cons x t) = x + W(t) + sum(t)$$

*Formalization.* `D5/S3/Combinatorics/PartitionWeightedSumReversal.weightedSum` (`✓ std3`).

*Citation.* Gus Wiseman (2023). *OEIS A362559, Number of integer partitions of n whose weighted sum is divisible by n*. URL: <https://oeis.org/A362559>.

*Commentary.*

The weight of a position is its one-based index, so the first entry carries weight one. Written without indices, adding an entry at the front contributes that entry once and raises every later weight by one, which is the total of the remaining entries. The source entry records the same quantity as the sum of the partial sums of the reverse.

**Definition 1.2 (Partitions of a total).**

$$Partition(n) = \{y \mid ((decreasing y) \land (positive y)) \land (sum(y) = n)\}$$

*Formalization.* `D5/S3/Combinatorics/PartitionWeightedSumReversal.IsPartition` (`✓ std3`).

*Citation.* Gus Wiseman (2023). *OEIS A362559, Number of integer partitions of n whose weighted sum is divisible by n*. URL: <https://oeis.org/A362559>.

*Commentary.*

A partition of a natural number is a weakly decreasing list of positive naturals with that total. The presentation matters only for the reading of the word reverse; the argument below uses neither the decrease nor the positivity.

**Definition 1.3 (The conjectured equivalence).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; \forall y \in Partition(n),\; (n \mid W(y)) \Leftrightarrow (n \mid W(reverse(y))))$$

*Formalization.* `D5/S3/Combinatorics/PartitionWeightedSumReversal.claim` (`✓ std3`).

*Citation.* Gus Wiseman (2023). *OEIS A362559, Number of integer partitions of n whose weighted sum is divisible by n*. URL: <https://oeis.org/A362559>.

*Commentary.*

The source asserts that a partition of a number has weighted sum divisible by that number exactly when its reverse does, and leaves the assertion unjudged on two of its entries.

**Theorem 1.4 (The equivalence holds).**

$$\forall n \in \mathrm{Nat},\; \forall y \in Partition(n),\; (n \mid W(y)) \Leftrightarrow (n \mid W(reverse(y)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PartitionWeightedSumReversal.result` (`✓ std3`). ∎

*Resolves.* `Problems/partition-weighted-sum-reversal` (proved) by `D5/S3/Combinatorics/PartitionWeightedSumReversal.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"partition-weighted-sum-reversal","declaration_gid":"D5/S3/Combinatorics/PartitionWeightedSumReversal.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman (2023). *OEIS A362559, Number of integer partitions of n whose weighted sum is divisible by n*. URL: <https://oeis.org/A362559>.

*Commentary.*

One identity carries everything: the weighted sum of a list and the weighted sum of its reverse add to one more than the length times the total. Reindexing the reversed sum sends the weight at a position to its complement, so the two weights at each entry add to one more than the length, and the entry-wise sum is that constant times the total. On a partition the total is the modulus, so the right-hand side is a multiple of it and the two weighted sums are congruent up to sign. Formally the identity follows from appending a single entry, which adds that entry weighted by one more than the current length, applied along the recursion for the reverse. Neither the decrease of the parts nor their positivity is used, so the hypothesis carries the correspondence to the source sentence and nothing else.

## References

- Truth anchor: `D5/S3/Combinatorics/PartitionWeightedSumReversal.IsPartition`
- Truth anchor: `D5/S3/Combinatorics/PartitionWeightedSumReversal.claim`
- Truth anchor: `D5/S3/Combinatorics/PartitionWeightedSumReversal.result`
- Truth anchor: `D5/S3/Combinatorics/PartitionWeightedSumReversal.weightedSum`
