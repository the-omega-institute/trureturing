# CompositionInversion

## Abstract

Stable A274190 diagonals and inversion of the unbordered-word series.

**Definition 1.1 (a274190).**

$$(\forall (n : \mathbb{N}) , \operatorname{a274190} n 0 = 1) \land (\forall (m : \mathbb{N}) , \operatorname{a274190} 0 (m + 1) = 0) \land (\forall (n m : \mathbb{N}) , \operatorname{a274190} (n + 1) (m + 1) = \operatorname{if} m + 1 \leq n + 1 \operatorname{then} \operatorname{a274190} n m + \operatorname{a274190} n (2 \cdot (m + 1)) \operatorname{else} 0)$$

*Formalization.* `D5/S1/Words/BlockPalindromes/CompositionInversion.a274190` (`✓ std3`).

*Citation.* D. Gabrić and J. Shallit (2023). *Smallest and Largest Block Palindrome Factorizations*. DOI: [10.1007/978-3-031-33180-0_14](https://doi.org/10.1007/978-3-031-33180-0_14). URL: <https://arxiv.org/abs/2302.13147>.

*Commentary.*

The recurrence is the A274190 triangle, with row zero and column zero included. Its reverse diagonal stabilizes to A274199.

**Theorem 1.2 (a274190_stable).**

$$\forall N d : \mathbb{N} , 2 \cdot d \leq N \Rightarrow \operatorname{a274190} N (N - d) = \operatorname{a274190} (2 \cdot d) d$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/CompositionInversion.a274190_stable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement holds for all of its quantified arguments.

**Theorem 1.3 (a274190_diagonal_limit).**

$$\forall (d : \mathbb{N}) , \operatorname{Tendsto} (\operatorname{fun} N : \mathbb{N} \mapsto (\operatorname{a274190} N (N - d) : \mathbb{R})) \operatorname{atTop} (\operatorname{nhds} (\operatorname{a274190} (2 \cdot d) d : \mathbb{R}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/CompositionInversion.a274190_diagonal_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement holds for all of its quantified arguments.

**Definition 1.4 (compCount).**

$$(\forall (b : \mathbb{N}) , \operatorname{compCount} 0 b = 1) \land (\forall (n b : \mathbb{N}) , \operatorname{compCount} (n + 1) b = \sum_{i \in \operatorname{Finset} . \operatorname{range} (n + 1)} \operatorname{if} i + 1 \leq b \operatorname{then} \operatorname{compCount} (n - i) (2 \cdot i + 1) \operatorname{else} 0)$$

*Formalization.* `D5/S1/Words/BlockPalindromes/CompositionInversion.compCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of compCount.

**Theorem 1.5 (a274190_compCount).**

$$\forall N m : \mathbb{N} , m \leq N \Rightarrow \operatorname{a274190} N m = \operatorname{compCount} (N - m) (m + 1)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/CompositionInversion.a274190_compCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The recurrence of the reverse triangle is the first-part recurrence for compositions whose next part is less than twice its predecessor.

**Theorem 1.6 (a274190_stable_compCount).**

$$\forall (d : \mathbb{N}) , \operatorname{a274190} (2 \cdot d) d = \operatorname{compCount} d d$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/CompositionInversion.a274190_stable_compCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement holds for all of its quantified arguments.

**Theorem 1.7 (compCount_fib_bound).**

$$\forall n b : \mathbb{N} , \operatorname{compCount} n b \leq \operatorname{Nat} . \operatorname{fib} (n + 1)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/CompositionInversion.compCount_fib_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The restricted composition count is at most Nat.fib(n+1). The bound gives absolute convergence at every reciprocal integer alphabet size k≥2.

**Theorem 1.8 (composition_series_summable).**

$$\forall (k : \mathbb{N}) , (2 \leq k) \Rightarrow (\operatorname{Summable} (\operatorname{fun} d : \mathbb{N} \mapsto (\operatorname{compCount} d d : \mathbb{R}) / (k : \mathbb{R}) ^{d}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/CompositionInversion.composition_series_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement holds for all of its quantified arguments.

**Definition 1.9 (compTerm).**

$$\forall (k : \mathbb{N}) , \forall (b : \mathbb{N}) , \forall (d : \mathbb{N}) , \operatorname{compTerm} k b d = (\operatorname{compCount} d b : \mathbb{R}) / (k : \mathbb{R}) ^{d}$$

*Formalization.* `D5/S1/Words/BlockPalindromes/CompositionInversion.compTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of compTerm.

**Definition 1.10 (totalSeries).**

$$\forall (k : \mathbb{N}) , \operatorname{totalSeries} k = \sum'_{d : \mathbb{N}} \operatorname{compTerm} k d d$$

*Formalization.* `D5/S1/Words/BlockPalindromes/CompositionInversion.totalSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of totalSeries.

**Theorem 1.11 (unbordered_composition_series).**

$$\forall (k : \mathbb{N}) , (2 \leq k) \Rightarrow (\operatorname{totalSeries} k = 1 / (1 - q k (\operatorname{uCount} k)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BlockPalindromes/CompositionInversion.unbordered_composition_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pairing the two regions j<2i and 2i≤j cancels their signed convolution contributions. The remaining identity relates the unbordered-word series to the full restricted-composition series.

## References

- Truth anchor: `D5/S1/Words/BlockPalindromes/CompositionInversion.a274190`
- Truth anchor: `D5/S1/Words/BlockPalindromes/CompositionInversion.a274190_compCount`
- Truth anchor: `D5/S1/Words/BlockPalindromes/CompositionInversion.a274190_diagonal_limit`
- Truth anchor: `D5/S1/Words/BlockPalindromes/CompositionInversion.a274190_stable`
- Truth anchor: `D5/S1/Words/BlockPalindromes/CompositionInversion.a274190_stable_compCount`
- Truth anchor: `D5/S1/Words/BlockPalindromes/CompositionInversion.compCount`
- Truth anchor: `D5/S1/Words/BlockPalindromes/CompositionInversion.compCount_fib_bound`
- Truth anchor: `D5/S1/Words/BlockPalindromes/CompositionInversion.compTerm`
- Truth anchor: `D5/S1/Words/BlockPalindromes/CompositionInversion.composition_series_summable`
- Truth anchor: `D5/S1/Words/BlockPalindromes/CompositionInversion.totalSeries`
- Truth anchor: `D5/S1/Words/BlockPalindromes/CompositionInversion.unbordered_composition_series`
- Dependency: [D5/S1/Words/BlockPalindromes/GreedyRenewal](GreedyRenewal.md)
