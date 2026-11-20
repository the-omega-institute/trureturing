# A four-wire obstruction in a sorting network

## Abstract

Chronological restrictions of reduced reversal words.

A state lists the wire labels at their current positions. The generator with zero-based index i swaps positions i and i+1. A reduced reversal word starts at the identity, ends at the reversal and has length n(n-1)/2. Every unordered pair of labels crosses once, from increasing to decreasing order.

**Theorem 1.1 (Distinct endpoints of a generator).**

$$left\left(i\right) \neq right\left(i\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/FriedenSortingNetwork.left_ne_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two positions have indices i and i+1.

**Theorem 1.2 (Rank of a retained crossing).**

$$restrictFrom\left(S, p, i:w\right) = retainIfSelected\left(S, p, i, rank\left(S, p, p\left(left\left(i\right)\right)\right) + 1, restrictFrom\left(S, step\left(p, i\right), w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/FriedenSortingNetwork.restrict_cons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Frieden, Pavlo Pylyavskyy, Leonid Rybnikov (2026). *The big cactus group, invariant tensors, and rectangular tableaux*. DOI: [10.48550/arXiv.2610.24842](https://doi.org/10.48550/arXiv.2610.24842). URL: <https://arxiv.org/html/2610.24842v1>.

*Commentary.*

The recursive restriction always advances the full state. It prepends the stated one-based letter precisely when both swapped labels belong to S. Rank counts selected labels strictly to the left of the left endpoint. This is the chronological subnetwork construction in Section 4.4.

**Theorem 1.3 (Ranks of two selected adjacent wires).**

$$p\left(left\left(i\right)\right) \in S \implies rank\left(S, p, p\left(right\left(i\right)\right)\right) = rank\left(S, p, p\left(left\left(i\right)\right)\right) + 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/FriedenSortingNetwork.rank_right_before` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The left endpoint adds exactly one selected label to the rank of the right endpoint.

**Theorem 1.4 (A repeated left generator forces a forbidden restriction).**

$$ReducedReversal\left(w\right) \land HasRightBlock\left(n, i\right) \land Omits\left(m, i, i + 1\right) \implies \exists S,card\left(S\right)=4 \land restrict\left(w, S\right) \in X$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/FriedenSortingNetwork.quartet_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Frieden, Pavlo Pylyavskyy, Leonid Rybnikov (2026). *The big cactus group, invariant tensors, and rectangular tableaux*. DOI: [10.48550/arXiv.2610.24842](https://doi.org/10.48550/arXiv.2610.24842). URL: <https://arxiv.org/html/2610.24842v1>.

*Commentary.*

The word w is u followed by i, m, i and v. The right block is nonempty when i+2<n. The middle list m omits i and i+1. Between the two uses of i, the wire at position i+1 stays fixed and the labels strictly to its right stay in that block. The two endpoint swaps and the unique intervening crossing in the left block yield letters 2, 1, 2. Choose one wire in the right block. It moves only right in the retained prefix and only left in the retained suffix. Its initial rank determines the complete restriction, one of 123212, 232123, 321232 and 212321.

**Theorem 1.5 (Rank at a dropped swap).**

$$a \in S \land Drops\left(S, p, i\right) \implies rank\left(S, step\left(p, i\right), a\right) = rank\left(S, p, a\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/FriedenSortingNetwork.rank_step_stay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each selected wire a, dropping a swap means at least one of its endpoints is unselected. No two selected wires change relative order.

**Theorem 1.6 (Rank after a move to the right).**

$$p\left(right\left(i\right)\right) \in S \implies rank\left(S, step\left(p, i\right), p\left(left\left(i\right)\right)\right) = rank\left(S, p, p\left(left\left(i\right)\right)\right) + 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/FriedenSortingNetwork.rank_step_move_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The left wire gains one selected predecessor when it crosses a selected right wire.

**Theorem 1.7 (Rank after a move to the left).**

$$p\left(left\left(i\right)\right) \in S \implies rank\left(S, step\left(p, i\right), p\left(right\left(i\right)\right)\right) = rank\left(S, p, p\left(left\left(i\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/FriedenSortingNetwork.rank_step_move_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The right wire takes the previous rank of the selected left wire.

**Theorem 1.8 (Rank of a wire outside the swap).**

$$OutsideSwap\left(a, p, i\right) \implies rank\left(S, step\left(p, i\right), a\right) = rank\left(S, p, a\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/FriedenSortingNetwork.rank_other` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

OutsideSwap means a is distinct from both swapped labels. Its relative order with respect to each selected wire is preserved.

**Theorem 1.9 (Number of moves of a wire).**

$$ReducedReversal\left(w\right) \implies length\left(wireDirections\left(id, a, w\right)\right) \le n-1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/FriedenSortingNetwork.wire_directions_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each wire a, each move has a distinct partner, and the partners all lie among the other n-1 wire labels.

## References

- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.left_ne_right`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.quartet_left`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.rank_other`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.rank_right_before`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.rank_step_move_left`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.rank_step_move_right`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.rank_step_stay`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.restrict_cons`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.wire_directions_bound`
