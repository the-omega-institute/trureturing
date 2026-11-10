# Ordered block allocations

## Abstract

Ordered allocations factor permutations and determine the first-block minimum mean.

**Definition 1.1 (Allocations with prescribed fiber sizes).**

$$\forall alpha \in Type,\; \forall iota \in Type,\; [\operatorname{Fintype}\left(alpha\right)] [\operatorname{DecidableEq}\left(iota\right)] \forall c \in alpha \to iota,\; \operatorname{Allocation}\left(c\right) = \{f: alpha \to iota \Vert \forall j \in iota,\; \operatorname{Fintype.card}\left(\{a: alpha \Vert f\left(a\right) = j\}\right) = \operatorname{Fintype.card}\left(\{a: alpha \Vert c\left(a\right) = j\}\right)\}$$

*Formalization.* `D5/S1/Words/Permutations/OrderedBlockAllocations.Allocation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An allocation assigns a label to every letter and has the same fiber cardinality at every label as c. The subtype retains the assignment and its cardinality equalities.

**Definition 1.2 (Increasing order in each block).**

$$\forall alpha \in Type,\; \forall iota \in Type,\; [\operatorname{LinearOrder}\left(alpha\right)] \forall c \in alpha \to iota,\; \forall pi \in \operatorname{Equiv.Perm}\left(alpha\right),\; \operatorname{IncreasingOnBlocks}\left(c, pi\right) = (\forall a \in alpha,\; \forall b \in alpha,\; c\left(a\right) = c\left(b\right) \implies a < b \implies pi\left(a\right) < pi\left(b\right))$$

*Formalization.* `D5/S1/Words/Permutations/OrderedBlockAllocations.IncreasingOnBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Positions with equal c-labels have their letters in strictly increasing order.

**Theorem 1.3 (The factorial factorization).**

$$\forall alpha \in Type,\; \forall iota \in Type,\; [\operatorname{Fintype}\left(alpha\right)] [\operatorname{LinearOrder}\left(alpha\right)] [\operatorname{Fintype}\left(iota\right)] [\operatorname{DecidableEq}\left(iota\right)] \forall c \in alpha \to iota,\; \operatorname{Fintype.card}\left(\operatorname{Allocation}\left(c\right)\right) \cdot (\prod_{j: iota} \operatorname{Nat.factorial}\left(\operatorname{Fintype.card}\left(\{a: alpha \Vert c\left(a\right) = j\}\right)\right)) = \operatorname{Nat.factorial}\left(\operatorname{Fintype.card}\left(alpha\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/OrderedBlockAllocations.allocation_card_factorial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every permutation determines its allocation by sorting the letters in each source fiber. The remaining choices are independent permutations internal to each fiber. This constructs a bijection and gives the cardinality factorization.

**Theorem 1.4 (The mean minimum of the first block).**

$$\forall n \in \mathbb{N},\; \forall hn \in 0 < n,\; \forall iota \in Type,\; [\operatorname{Fintype}\left(iota\right)] [\operatorname{DecidableEq}\left(iota\right)] \forall c \in \operatorname{Fin}\left(n\right) \to iota,\; (\operatorname{Nat.cast}\left(\operatorname{Fintype.card}\left(\{a: \operatorname{Fin}\left(n\right) \Vert c\left(a\right) = c\left(\operatorname{Fin.mk}\left(0, hn\right)\right)\}\right) + 1\right): \mathbb{Q}) \cdot (\sum_{p: \{pi: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right) \Vert \operatorname{IncreasingOnBlocks}\left(c, pi\right)\}} (\operatorname{Nat.cast}\left((\operatorname{if} h: 0 < n \operatorname{then} \operatorname{val}\left(\operatorname{val}\left(p\right)\left(\operatorname{Fin.mk}\left(0, h\right)\right)\right) + 1 \operatorname{else} 0)\right): \mathbb{Q})) = ((\operatorname{Nat.cast}\left(n\right): \mathbb{Q}) + 1) \cdot (\operatorname{Nat.cast}\left(\operatorname{Fintype.card}\left(\{pi: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right) \Vert \operatorname{IncreasingOnBlocks}\left(c, pi\right)\}\right)\right): \mathbb{Q})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/OrderedBlockAllocations.weighted_increasing_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first letter is the minimum of the letters allocated to the block containing position zero. For a positive d-element subset of {0,...,n-1}, summing its minimum plus one gives Nat.choose (n+1) (d+1). Equally sized fibers of allocations then give this weighted identity.

**Theorem 1.5 (Sorting identifies the two cardinalities).**

$$\forall alpha \in Type,\; \forall iota \in Type,\; [\operatorname{Fintype}\left(alpha\right)] [\operatorname{LinearOrder}\left(alpha\right)] [\operatorname{Fintype}\left(iota\right)] [\operatorname{DecidableEq}\left(iota\right)] \forall c \in alpha \to iota,\; \operatorname{Fintype.card}\left(\{pi: \operatorname{Equiv.Perm}\left(alpha\right) \Vert \operatorname{IncreasingOnBlocks}\left(c, pi\right)\}\right) = \operatorname{Fintype.card}\left(\operatorname{Allocation}\left(c\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/OrderedBlockAllocations.card_increasingOnBlocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sorting each allocated fiber is inverse to extracting labels with the inverse permutation.

## References

- Truth anchor: `D5/S1/Words/Permutations/OrderedBlockAllocations.Allocation`
- Truth anchor: `D5/S1/Words/Permutations/OrderedBlockAllocations.IncreasingOnBlocks`
- Truth anchor: `D5/S1/Words/Permutations/OrderedBlockAllocations.allocation_card_factorial`
- Truth anchor: `D5/S1/Words/Permutations/OrderedBlockAllocations.card_increasingOnBlocks`
- Truth anchor: `D5/S1/Words/Permutations/OrderedBlockAllocations.weighted_increasing_blocks`
