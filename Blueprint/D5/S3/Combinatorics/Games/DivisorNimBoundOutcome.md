# Dyadic Depth and Zero Positions

## Abstract

A position has zero Sprague–Grundy value precisely when an even number of heaps attain its least dyadic valuation.

**Definition 1.1 (Dyadic valuation).**

$$\forall h \in \mathrm{Nat},\; \operatorname{valuation}\left(h\right) = \operatorname{padicValNat}\left(2, h\right)$$

*Formalization.* `D5/S3/Combinatorics/Games/DivisorNimBoundOutcome.valuation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The dyadic valuation of a positive integer is the exponent of two in its prime factorization.

**Definition 1.2 (Position depth).**

$$\forall P \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; \forall k \in \mathrm{Nat},\; \operatorname{HasDepth}\left(P, k\right) \Leftrightarrow \left(\left(\forall h \in \mathrm{Nat},\; \operatorname{mem}\left(h, P\right) \Rightarrow k \le \operatorname{valuation}\left(h\right)\right) \land \left(\exists h \in \mathrm{Nat},\; \operatorname{mem}\left(h, P\right) \land \operatorname{valuation}\left(h\right) = k\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Games/DivisorNimBoundOutcome.HasDepth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every heap has valuation at least k, and at least one heap has valuation exactly k.

**Definition 1.3 (Heaps at a depth).**

$$\forall P \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; \forall k \in \mathrm{Nat},\; \operatorname{countAt}\left(P, k\right) = \operatorname{card}\left(\{h \in P | \operatorname{valuation}\left(h\right) = k\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Games/DivisorNimBoundOutcome.countAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Count heap occurrences of valuation k, retaining their multiplicities.

**Theorem 1.4 (Subtracting at a lower valuation).**

$$\forall h \in \mathrm{Nat},\; \forall d \in \mathrm{Nat},\; \left(0 < d \land \left(d \le h \land \operatorname{valuation}\left(d\right) < \operatorname{valuation}\left(h\right)\right)\right) \Rightarrow \left(0 < h - d \land \operatorname{valuation}\left(h - d\right) = \operatorname{valuation}\left(d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundOutcome.valuation_sub_of_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the removed amount has smaller valuation than the heap, the positive remainder has the valuation of that amount.

**Theorem 1.5 (Lower-depth moves create one minimum heap).**

$$\forall P \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; \forall h \in \mathrm{Nat},\; \forall d \in \mathrm{Nat},\; \forall j \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \left(\left(\operatorname{Positive}\left(P\right) \land \left(\operatorname{HasDepth}\left(P, k\right) \land \left(\operatorname{mem}\left(h, P\right) \land \operatorname{legal}\left(P, h, d\right)\right)\right)\right) \land \left(\operatorname{valuation}\left(d\right) = j \land j < k\right)\right) \Rightarrow \left(\operatorname{HasDepth}\left(\operatorname{successor}\left(P, h, d\right), j\right) \land \operatorname{countAt}\left(\operatorname{successor}\left(P, h, d\right), j\right) = 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundOutcome.lower_move` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A removal of valuation j below the position depth creates exactly one heap at depth j. Every unchanged heap remains at greater depth.

**Theorem 1.6 (Equal-valuation subtraction).**

$$\forall h \in \mathrm{Nat},\; \forall d \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \left(0 < h \land \left(0 < d \land \left(d \le h \land \left(\operatorname{valuation}\left(h\right) = k \land \left(\operatorname{valuation}\left(d\right) = k \land \left(\neg h - d = 0\right)\right)\right)\right)\right)\right) \Rightarrow k < \operatorname{valuation}\left(h - d\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundOutcome.valuation_sub_same` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtracting two positive integers of the same dyadic valuation either gives zero or raises the valuation.

**Theorem 1.7 (Moves retaining a minimum heap change parity).**

$$\forall P \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; \forall h \in \mathrm{Nat},\; \forall d \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \left(\left(\operatorname{Positive}\left(P\right) \land \left(\operatorname{HasDepth}\left(P, k\right) \land \left(\operatorname{mem}\left(h, P\right) \land \operatorname{legal}\left(P, h, d\right)\right)\right)\right) \land \left(k \le \operatorname{valuation}\left(d\right) \land 0 < \operatorname{countAt}\left(\operatorname{erase}\left(P, h\right), k\right)\right)\right) \Rightarrow \left(\operatorname{HasDepth}\left(\operatorname{successor}\left(P, h, d\right), k\right) \land \operatorname{mod}\left(\operatorname{countAt}\left(\operatorname{successor}\left(P, h, d\right), k\right) + \operatorname{countAt}\left(P, k\right), 2\right) = 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundOutcome.high_move_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If an unchanged heap retains the minimum depth, any removal at least that deep has valuation exactly equal to the depth. It either adds or removes one minimum-depth heap, so the count changes parity.

**Theorem 1.8 (Every move from an even count has an odd count).**

$$\forall P \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; \forall Q \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; \forall k \in \mathrm{Nat},\; \left(\operatorname{Positive}\left(P\right) \land \left(\operatorname{HasDepth}\left(P, k\right) \land \left(\operatorname{Even}\left(\operatorname{countAt}\left(P, k\right)\right) \land \operatorname{mem}\left(Q, \operatorname{moves}\left(P\right)\right)\right)\right)\right) \Rightarrow \left(\exists j \in \mathrm{Nat},\; \operatorname{HasDepth}\left(Q, j\right) \land \operatorname{mod}\left(\operatorname{countAt}\left(Q, j\right), 2\right) = 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundOutcome.even_count_moves_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An even positive minimum-depth count is at least two. A lower removal creates a single minimum; every other legal removal leaves a minimum heap and changes the parity of its count.

**Theorem 1.9 (An odd count has a zero-count follower).**

$$\forall P \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; \forall k \in \mathrm{Nat},\; \left(\operatorname{Positive}\left(P\right) \land \left(\operatorname{HasDepth}\left(P, k\right) \land \operatorname{mod}\left(\operatorname{countAt}\left(P, k\right), 2\right) = 1\right)\right) \Rightarrow \left(\exists Q \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; \operatorname{mem}\left(Q, \operatorname{moves}\left(P\right)\right) \land \left(Q = 0 \lor \left(\exists j \in \mathrm{Nat},\; \operatorname{HasDepth}\left(Q, j\right) \land \operatorname{Even}\left(\operatorname{countAt}\left(Q, j\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundOutcome.odd_count_has_even_move` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With at least three minimum-depth heaps, subtract the depth power from one of them. With a unique minimum and another heap, subtract that power from the other heap. A singleton is removed entirely.

**Theorem 1.10 (Zero value is equivalent to an even count).**

$$\forall P \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; \forall k \in \mathrm{Nat},\; \left(\operatorname{Positive}\left(P\right) \land \operatorname{HasDepth}\left(P, k\right)\right) \Rightarrow \left(\operatorname{grundy}\left(P\right) = 0 \Leftrightarrow \operatorname{Even}\left(\operatorname{countAt}\left(P, k\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundOutcome.zero_iff_even_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on the total number of stones applies the mex rule to the two parity properties: an even count has no zero-valued follower, while an odd count has a zero-valued follower.

**Theorem 1.11 (Nonzero high-removal followers require a unique minimum).**

$$\forall P \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; \forall h \in \mathrm{Nat},\; \forall d \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \left(\left(\operatorname{Positive}\left(P\right) \land \left(\operatorname{HasDepth}\left(P, k\right) \land \left(\operatorname{mem}\left(h, P\right) \land \operatorname{legal}\left(P, h, d\right)\right)\right)\right) \land \left(k \le \operatorname{valuation}\left(d\right) \land \left(\left(\neg \operatorname{grundy}\left(P\right) = 0\right) \land \left(\neg \operatorname{grundy}\left(\operatorname{successor}\left(P, h, d\right)\right) = 0\right)\right)\right)\right) \Rightarrow \left(\operatorname{countAt}\left(P, k\right) = 1 \land \operatorname{valuation}\left(h\right) = k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundOutcome.high_nonzero_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero parent, a high removal retaining a minimum-depth heap would change an odd count to an even count and produce value zero. Thus a nonzero follower can arise only by changing the unique minimum.

**Theorem 1.12 (Power of two times an odd factor).**

$$\forall m \in \mathrm{Nat},\; 0 < m \Rightarrow \left(\exists u \in \mathrm{Nat},\; 0 < u \land \left(\operatorname{Odd}\left(u\right) \land m = 2^{\operatorname{valuation}\left(m\right)} \cdot u\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundOutcome.valuation_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive heap size is a power of two times a positive odd integer.

**Theorem 1.13 (At least two odd heaps give value at most one).**

$$\forall P \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; \left(\operatorname{Positive}\left(P\right) \land \left(\operatorname{HasDepth}\left(P, 0\right) \land 1 < \operatorname{countAt}\left(P, 0\right)\right)\right) \Rightarrow \operatorname{grundy}\left(P\right) \le 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundOutcome.depth_zero_multiple` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are no lower-valuation removals at depth zero. With more than one odd heap, every follower of a nonzero parent has value zero.

## References

- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundOutcome.HasDepth`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundOutcome.countAt`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundOutcome.depth_zero_multiple`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundOutcome.even_count_moves_odd`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundOutcome.high_move_count`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundOutcome.high_nonzero_unique`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundOutcome.lower_move`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundOutcome.odd_count_has_even_move`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundOutcome.valuation`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundOutcome.valuation_decomposition`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundOutcome.valuation_sub_of_lt`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundOutcome.valuation_sub_same`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundOutcome.zero_iff_even_count`
- Dependency: [D5/S3/Combinatorics/Games/DivisorNimGrundy](DivisorNimGrundy.md)
