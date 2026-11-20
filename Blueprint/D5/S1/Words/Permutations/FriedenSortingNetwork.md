# A four-wire obstruction in a sorting network

## Abstract

Chronological restrictions of reduced reversal words.

A state lists the wire labels at their current positions. The generator with zero-based index i swaps positions i and i+1. A reduced reversal word starts at the identity, ends at the reversal and has length n(n-1)/2 with natural-number division. Every unordered pair of labels crosses once, from increasing to decreasing order. In the formulas, n is natural, i and j are generators, p is a state, S is a finite set of labels, a is a label, and u, m, v and w are words on n wires.

**Definition 1.1 (Adjacent-swap words).**

$$\forall n \in \mathbb{N},\; \operatorname{Word}\left(n\right) = \operatorname{List}\left(\operatorname{Fin}\left(n-1\right)\right)$$

*Formalization.* `D5/S1/Words/Permutations/FriedenSortingNetwork.Word` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finite lists of generators with zero-based indices below n-1.

**Definition 1.2 (Wire state).**

$$\forall n \in \mathbb{N},\; \operatorname{State}\left(n\right) = \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right)$$

*Formalization.* `D5/S1/Words/Permutations/FriedenSortingNetwork.State` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A permutation sending each position to the label currently there.

**Definition 1.3 (Path orientation).**

$$\forall n \in \mathbb{N},\; \operatorname{Orientation}\left(n\right) = \operatorname{Fin}\left(n-2\right)\to\operatorname{Bool}$$

*Formalization.* `D5/S1/Words/Permutations/FriedenSortingNetwork.Orientation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One Boolean for each edge between consecutive generators.

**Definition 1.4 (Left position).**

$$\forall n \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(n-1\right),\; \operatorname{left}\left(i\right) : \operatorname{Fin}\left(n\right)$$

*Formalization.* `D5/S1/Words/Permutations/FriedenSortingNetwork.left` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The position whose index is the generator's index.

**Definition 1.5 (Right position).**

$$\forall n \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(n-1\right),\; \operatorname{right}\left(i\right) : \operatorname{Fin}\left(n\right)$$

*Formalization.* `D5/S1/Words/Permutations/FriedenSortingNetwork.right` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The position one greater than the generator's index.

**Definition 1.6 (Adjacent swap).**

$$\forall n \in \mathbb{N},\; \forall p \in \operatorname{State}\left(n\right),\; \forall i \in \operatorname{Fin}\left(n-1\right),\; \operatorname{step}\left(p, i\right) = p\circ\operatorname{swap}\left(\operatorname{left}\left(i\right), \operatorname{right}\left(i\right)\right)$$

*Formalization.* `D5/S1/Words/Permutations/FriedenSortingNetwork.step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Swap the two positions before reading their labels in the current state.

**Definition 1.7 (Crossing endpoints).**

$$\forall n \in \mathbb{N},\; \forall p \in \operatorname{State}\left(n\right),\; \forall i \in \operatorname{Fin}\left(n-1\right),\; \operatorname{endpoints}\left(p, i\right) = (p\left(\operatorname{left}\left(i\right)\right),p\left(\operatorname{right}\left(i\right)\right))$$

*Formalization.* `D5/S1/Words/Permutations/FriedenSortingNetwork.endpoints` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The labels at the two positions before the swap, ordered left to right.

**Definition 1.8 (Chronological crossing pairs).**

$$\forall n \in \mathbb{N},\; \forall p \in \operatorname{State}\left(n\right),\; \forall w \in \operatorname{Word}\left(n\right),\; \operatorname{crossingPairsFrom}\left(p, w\right) : \operatorname{List}\left(\operatorname{Fin}\left(n\right)\times\operatorname{Fin}\left(n\right)\right)$$

*Formalization.* `D5/S1/Words/Permutations/FriedenSortingNetwork.crossingPairsFrom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Record both labels before each swap while advancing the state through the word.

**Definition 1.9 (Restriction from a state).**

$$\forall n \in \mathbb{N},\; \forall S \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall p \in \operatorname{State}\left(n\right),\; \forall w \in \operatorname{Word}\left(n\right),\; \operatorname{restrictFrom}\left(S, p, w\right) : \operatorname{List}\left(\mathbb{N}\right)$$

*Formalization.* `D5/S1/Words/Permutations/FriedenSortingNetwork.restrictFrom` (`✓ std3`).

*Citation.* Gabriel Frieden, Pavlo Pylyavskyy, Leonid Rybnikov (2026). *The big cactus group, invariant tensors, and rectangular tableaux*. DOI: [10.48550/arXiv.2610.24842](https://doi.org/10.48550/arXiv.2610.24842). URL: <https://arxiv.org/html/2610.24842v1>.

*Commentary.*

Advance the state at every swap. Record a letter only when both labels lie in the selected set. Use one plus the number of selected labels strictly to the left of the swapped positions.

**Definition 1.10 (Induced subnetwork).**

$$\forall n \in \mathbb{N},\; \forall w \in \operatorname{Word}\left(n\right),\; \forall S \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{restrict}\left(w, S\right) = \operatorname{restrictFrom}\left(S, \operatorname{id}, w\right)$$

*Formalization.* `D5/S1/Words/Permutations/FriedenSortingNetwork.restrict` (`✓ std3`).

*Citation.* Gabriel Frieden, Pavlo Pylyavskyy, Leonid Rybnikov (2026). *The big cactus group, invariant tensors, and rectangular tableaux*. DOI: [10.48550/arXiv.2610.24842](https://doi.org/10.48550/arXiv.2610.24842). URL: <https://arxiv.org/html/2610.24842v1>.

*Commentary.*

Start the restriction at the identity state.

**Definition 1.11 (The four forbidden words).**

$$\operatorname{forbidden} = [[1,2,3,2,1,2],[3,2,1,2,3,2],[2,1,2,3,2,1],[2,3,2,1,2,3]]$$

*Formalization.* `D5/S1/Words/Permutations/FriedenSortingNetwork.forbidden` (`✓ std3`).

*Citation.* Gabriel Frieden, Pavlo Pylyavskyy, Leonid Rybnikov (2026). *The big cactus group, invariant tensors, and rectangular tableaux*. DOI: [10.48550/arXiv.2610.24842](https://doi.org/10.48550/arXiv.2610.24842). URL: <https://arxiv.org/html/2610.24842v1>.

*Commentary.*

The one-based chronological words 123212, 321232, 212321 and 232123.

**Definition 1.12 (Four-wire avoidance).**

$$\forall n \in \mathbb{N},\; \forall w \in \operatorname{Word}\left(n\right),\; \operatorname{AvoidsX}\left(w\right) \iff \forall S \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{card}\left(S\right) = 4 \implies \neg(\operatorname{restrict}\left(w, S\right) \in \operatorname{forbidden})$$

*Formalization.* `D5/S1/Words/Permutations/FriedenSortingNetwork.AvoidsX` (`✓ std3`).

*Citation.* Gabriel Frieden, Pavlo Pylyavskyy, Leonid Rybnikov (2026). *The big cactus group, invariant tensors, and rectangular tableaux*. DOI: [10.48550/arXiv.2610.24842](https://doi.org/10.48550/arXiv.2610.24842). URL: <https://arxiv.org/html/2610.24842v1>.

*Commentary.*

Every four-element set of labels gives a restriction outside forbidden.

**Definition 1.13 (Reduced reversal word).**

$$\forall n \in \mathbb{N},\; \forall w \in \operatorname{Word}\left(n\right),\; \operatorname{ReducedReversal}\left(w\right) \iff \operatorname{length}\left(w\right) = \lfloor n\cdot(n-1)/2\rfloor \land \operatorname{foldl}\left(\operatorname{step}, \operatorname{id}, w\right) = \operatorname{revPerm}$$

*Formalization.* `D5/S1/Words/Permutations/FriedenSortingNetwork.ReducedReversal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The length is n(n-1)/2 in natural numbers, and folding step from the identity gives the reversal.

**Definition 1.14 (Selected predecessors).**

$$\forall n \in \mathbb{N},\; \forall S \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall p \in \operatorname{State}\left(n\right),\; \forall a \in \operatorname{Fin}\left(n\right),\; \operatorname{below}\left(S, p, a\right) : \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)$$

*Formalization.* `D5/S1/Words/Permutations/FriedenSortingNetwork.below` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selected labels strictly to the left of the given label.

**Definition 1.15 (Rank in the selected order).**

$$\forall n \in \mathbb{N},\; \forall S \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall p \in \operatorname{State}\left(n\right),\; \forall a \in \operatorname{Fin}\left(n\right),\; \operatorname{rank}\left(S, p, a\right) = \operatorname{card}\left(\operatorname{below}\left(S, p, a\right)\right)$$

*Formalization.* `D5/S1/Words/Permutations/FriedenSortingNetwork.rank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cardinality of the selected predecessor set.

**Definition 1.16 (Chronological movements of a wire).**

$$\forall n \in \mathbb{N},\; \forall p \in \operatorname{State}\left(n\right),\; \forall a \in \operatorname{Fin}\left(n\right),\; \forall w \in \operatorname{Word}\left(n\right),\; \operatorname{wireDirections}\left(p, a, w\right) : \operatorname{List}\left(\operatorname{Bool}\right)$$

*Formalization.* `D5/S1/Words/Permutations/FriedenSortingNetwork.wireDirections` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Keep the swaps involving the given label. Record true for a move right and false for a move left.

**Theorem 1.17 (Distinct endpoints of a generator).**

$$\forall n \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(n-1\right),\; \operatorname{left}\left(i\right) \neq \operatorname{right}\left(i\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/FriedenSortingNetwork.left_ne_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two positions have indices i and i+1.

**Theorem 1.18 (Rank of a retained crossing).**

$$\forall n \in \mathbb{N},\; \forall S \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall p \in \operatorname{State}\left(n\right),\; \forall i \in \operatorname{Fin}\left(n-1\right),\; \forall w \in \operatorname{Word}\left(n\right),\; \operatorname{restrictFrom}\left(S, p, i :: w\right) = \operatorname{ite}\left(p\left(\operatorname{left}\left(i\right)\right) \in S \land p\left(\operatorname{right}\left(i\right)\right) \in S, \operatorname{rank}\left(S, p, p\left(\operatorname{left}\left(i\right)\right)\right) + 1 :: \operatorname{restrictFrom}\left(S, \operatorname{step}\left(p, i\right), w\right), \operatorname{restrictFrom}\left(S, \operatorname{step}\left(p, i\right), w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/FriedenSortingNetwork.restrict_cons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Frieden, Pavlo Pylyavskyy, Leonid Rybnikov (2026). *The big cactus group, invariant tensors, and rectangular tableaux*. DOI: [10.48550/arXiv.2610.24842](https://doi.org/10.48550/arXiv.2610.24842). URL: <https://arxiv.org/html/2610.24842v1>.

*Commentary.*

The recursive restriction always advances the full state. It prepends the stated one-based letter precisely when both swapped labels belong to S. Rank counts selected labels strictly to the left of the left endpoint. This is the chronological subnetwork construction in Section 4.4.

**Theorem 1.19 (Ranks at adjacent positions with the left wire selected).**

$$\forall n \in \mathbb{N},\; \forall S \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall p \in \operatorname{State}\left(n\right),\; \forall i \in \operatorname{Fin}\left(n-1\right),\; p\left(\operatorname{left}\left(i\right)\right) \in S \implies \operatorname{rank}\left(S, p, p\left(\operatorname{right}\left(i\right)\right)\right) = \operatorname{rank}\left(S, p, p\left(\operatorname{left}\left(i\right)\right)\right) + 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/FriedenSortingNetwork.rank_right_before` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The left endpoint adds exactly one selected label to the rank of the right endpoint.

**Theorem 1.20 (A repeated left generator forces a forbidden restriction).**

$$\forall n \in \mathbb{N},\; \forall u \in \operatorname{Word}\left(n\right),\; \forall m \in \operatorname{Word}\left(n\right),\; \forall v \in \operatorname{Word}\left(n\right),\; \forall i \in \operatorname{Fin}\left(n-1\right),\; (i.\operatorname{val} + 2<n \land (\forall j \in \operatorname{Fin}\left(n-1\right),\; j \in m \implies j.\operatorname{val} \neq i.\operatorname{val} \land j.\operatorname{val} \neq i.\operatorname{val} + 1) \land \operatorname{ReducedReversal}\left(u ++ (i :: m ++ i :: v)\right)) \implies (\exists S \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{card}\left(S\right)=4 \land \operatorname{restrict}\left(u ++ (i :: m ++ i :: v), S\right) \in \operatorname{forbidden})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/FriedenSortingNetwork.quartet_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Frieden, Pavlo Pylyavskyy, Leonid Rybnikov (2026). *The big cactus group, invariant tensors, and rectangular tableaux*. DOI: [10.48550/arXiv.2610.24842](https://doi.org/10.48550/arXiv.2610.24842). URL: <https://arxiv.org/html/2610.24842v1>.

*Commentary.*

The repeated word is u followed by i, m, i and v. The right block is nonempty when the index of i plus two is below n. The middle list m omits i and the generator with index one greater than i. Between the two uses of i, the wire at position i+1 stays fixed and the labels strictly to its right stay in that block. The two endpoint swaps and the unique intervening crossing in the left block yield letters 2, 1, 2. Choose one wire in the right block. It moves only right in the retained prefix and only left in the retained suffix. Its initial rank determines the complete restriction, one of 123212, 232123, 321232 and 212321.

**Theorem 1.21 (Rank at a dropped swap).**

$$\forall n \in \mathbb{N},\; \forall S \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall p \in \operatorname{State}\left(n\right),\; \forall i \in \operatorname{Fin}\left(n-1\right),\; \forall a \in \operatorname{Fin}\left(n\right),\; (a \in S \land \neg(p\left(\operatorname{left}\left(i\right)\right) \in S \land p\left(\operatorname{right}\left(i\right)\right) \in S)) \implies \operatorname{rank}\left(S, \operatorname{step}\left(p, i\right), a\right) = \operatorname{rank}\left(S, p, a\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/FriedenSortingNetwork.rank_step_stay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each selected wire a, dropping a swap means at least one of its endpoints is unselected. No two selected wires change relative order.

**Theorem 1.22 (Rank after a move to the right).**

$$\forall n \in \mathbb{N},\; \forall S \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall p \in \operatorname{State}\left(n\right),\; \forall i \in \operatorname{Fin}\left(n-1\right),\; p\left(\operatorname{right}\left(i\right)\right) \in S \implies \operatorname{rank}\left(S, \operatorname{step}\left(p, i\right), p\left(\operatorname{left}\left(i\right)\right)\right) = \operatorname{rank}\left(S, p, p\left(\operatorname{left}\left(i\right)\right)\right) + 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/FriedenSortingNetwork.rank_step_move_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The left wire gains one selected predecessor when it crosses a selected right wire.

**Theorem 1.23 (Rank after a move to the left).**

$$\forall n \in \mathbb{N},\; \forall S \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall p \in \operatorname{State}\left(n\right),\; \forall i \in \operatorname{Fin}\left(n-1\right),\; p\left(\operatorname{left}\left(i\right)\right) \in S \implies \operatorname{rank}\left(S, \operatorname{step}\left(p, i\right), p\left(\operatorname{right}\left(i\right)\right)\right) = \operatorname{rank}\left(S, p, p\left(\operatorname{left}\left(i\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/FriedenSortingNetwork.rank_step_move_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The right wire takes the previous rank of the selected left wire.

**Theorem 1.24 (Rank of a wire outside the swap).**

$$\forall n \in \mathbb{N},\; \forall S \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall p \in \operatorname{State}\left(n\right),\; \forall i \in \operatorname{Fin}\left(n-1\right),\; \forall a \in \operatorname{Fin}\left(n\right),\; (p\left(\operatorname{left}\left(i\right)\right) \neq a \land p\left(\operatorname{right}\left(i\right)\right) \neq a) \implies \operatorname{rank}\left(S, \operatorname{step}\left(p, i\right), a\right) = \operatorname{rank}\left(S, p, a\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/FriedenSortingNetwork.rank_other` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A label distinct from both swapped labels preserves its order relative to each selected wire.

**Theorem 1.25 (Number of moves of a wire).**

$$\forall n \in \mathbb{N},\; \forall w \in \operatorname{Word}\left(n\right),\; \forall a \in \operatorname{Fin}\left(n\right),\; \operatorname{ReducedReversal}\left(w\right) \implies \operatorname{length}\left(\operatorname{wireDirections}\left(\operatorname{id}, a, w\right)\right) \le n-1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/FriedenSortingNetwork.wire_directions_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each wire a, each move has a distinct partner, and the partners all lie among the other n-1 wire labels.

## References

- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.AvoidsX`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.Orientation`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.ReducedReversal`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.State`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.Word`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.below`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.crossingPairsFrom`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.endpoints`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.forbidden`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.left`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.left_ne_right`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.quartet_left`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.rank`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.rank_other`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.rank_right_before`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.rank_step_move_left`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.rank_step_move_right`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.rank_step_stay`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.restrict`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.restrictFrom`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.restrict_cons`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.right`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.step`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.wireDirections`
- Truth anchor: `D5/S1/Words/Permutations/FriedenSortingNetwork.wire_directions_bound`
