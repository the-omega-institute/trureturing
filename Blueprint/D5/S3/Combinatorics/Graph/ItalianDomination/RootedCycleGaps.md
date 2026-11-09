# RootedCycleGaps

## Abstract

Cutting at marked zeros relates labelled cyclic words to ordered gaps, and marking identities remove the root.

**Definition 1.1 (Zero Free Words).**

$$\forall (c a : \mathbb{N}) , \operatorname{ZeroFreeWords} c a = \{y : \operatorname{Fin} (c + a + 1) \to \operatorname{Fin} 3 \mid (\forall i , y i \neq 0) \land \operatorname{IsDeficit} y \land \operatorname{labelCount} y 1 = c + 1 \land \operatorname{labelCount} y 2 = a\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/ItalianDomination/RootedCycleGaps.ZeroFreeWords` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

These valid cyclic deficit maps contain no zero, c+1 ones and a twos.

**Theorem 1.2 (zero Free cycle marking count).**

$$\forall (c a : \mathbb{N}) , (c + 1) * \operatorname{Nat}.\operatorname{card} (\operatorname{ZeroFreeWords} c a) = (c + a + 1) * (c + 1) . \operatorname{choose} a$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ItalianDomination/RootedCycleGaps.zeroFree_cycle_marking_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

Marking a one in each zero-free cyclic word equates its labelled count with the rooted ordinary-word count.

**Definition 1.3 (Rooted Refined Cycle).**

$$\forall (N m b c a : \mathbb{N}) , \operatorname{RootedRefinedCycle} N m b c a = \{y : \operatorname{Fin} (N + 1) \to \operatorname{Fin} 3 \mid y 0 = 0 \land \operatorname{IsDeficit} y \land \operatorname{labelCount} y 0 = m \land \operatorname{labelCount} y 1 = c \land \operatorname{labelCount} y 2 = a + 2 * b \land \operatorname{doubleTwoCount} y = b\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/ItalianDomination/RootedCycleGaps.RootedRefinedCycle` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

These valid cyclic deficit maps have a zero at vertex zero and the indicated label and adjacent-pair inventories.

**Theorem 1.4 (rooted Refined Cycle card).**

$$\forall (N m b c a : \mathbb{N}) , (0 < m) \to (N + 1 = m + c + a + 2 * b) \to \operatorname{Nat}.\operatorname{card} (\operatorname{RootedRefinedCycle} N m b c a) = m . \operatorname{choose} b * (c + (m - b) - 1) . \operatorname{choose} c * (c + (m - b)) . \operatorname{choose} a$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ItalianDomination/RootedCycleGaps.rootedRefinedCycle_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

Fix a zero at vertex zero. Cutting at the zeros gives ordered gaps. Choose the exceptional gaps, distribute the ones among the ordinary gaps and select the slots containing isolated twos.

**Definition 1.5 (Refined Cycle).**

$$\forall (N m b c a : \mathbb{N}) , \operatorname{RefinedCycle} N m b c a = \{y : \operatorname{Fin} (N + 1) \to \operatorname{Fin} 3 \mid \operatorname{IsDeficit} y \land \operatorname{labelCount} y 0 = m \land \operatorname{labelCount} y 1 = c \land \operatorname{labelCount} y 2 = a + 2 * b \land \operatorname{doubleTwoCount} y = b\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/ItalianDomination/RootedCycleGaps.RefinedCycle` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

These valid cyclic deficit maps have the indicated label and adjacent-pair inventories.

**Theorem 1.6 (refined cycle marking count).**

$$\forall (N m b c a : \mathbb{N}) , (0 < m) \to (N + 1 = m + c + a + 2 * b) \to m * \operatorname{Nat}.\operatorname{card} (\operatorname{RefinedCycle} N m b c a) = (N + 1) * (m . \operatorname{choose} b * (c + (m - b) - 1) . \operatorname{choose} c * (c + (m - b)) . \operatorname{choose} a)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ItalianDomination/RootedCycleGaps.refined_cycle_marking_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

Marking a zero equates the refined labelled-cycle count with the rooted gap count.

**Theorem 1.7 (label Count sum).**

$$\forall (n : \mathbb{N}) (y : \operatorname{Fin} n \to \operatorname{Fin} 3) , \operatorname{labelCount} y 0 + \operatorname{labelCount} y 1 + \operatorname{labelCount} y 2 = n$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ItalianDomination/RootedCycleGaps.labelCount_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

The three label classes partition the labelled vertices.

**Theorem 1.8 (weight eq label Count).**

$$\forall (n : \mathbb{N}) (y : \operatorname{Fin} n \to \operatorname{Fin} 3) , (\sum_{i : \operatorname{Fin} n} (y i) . \operatorname{val}) = \operatorname{labelCount} y 1 + 2 * \operatorname{labelCount} y 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ItalianDomination/RootedCycleGaps.weight_eq_labelCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

The sum of the labels is the number of ones plus twice the number of twos.

**Theorem 1.9 (zero Free twos le ones).**

$$\forall (n : \mathbb{N}) (y : \operatorname{Fin} n \to \operatorname{Fin} 3) , (\forall i , y i \neq 0) \to (\operatorname{IsDeficit} y) \to \operatorname{labelCount} y 2 \leq \operatorname{labelCount} y 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ItalianDomination/RootedCycleGaps.zeroFree_twos_le_ones` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

In a valid zero-free cyclic map every two is followed by a one, giving an injection into the one-labelled vertices.

**Theorem 1.10 (zero Containing inventory bounds).**

$$\forall (N : \mathbb{N}) (y : \operatorname{Fin} (N + 1) \to \operatorname{Fin} 3) , (\operatorname{IsDeficit} y) \to (\exists i , y i = 0) \to \operatorname{doubleTwoCount} y \leq \operatorname{labelCount} y 0 \land 2 * \operatorname{doubleTwoCount} y \leq \operatorname{labelCount} y 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ItalianDomination/RootedCycleGaps.zeroContaining_inventory_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

Every adjacent pair of twos determines a zero gap and contributes two twos to the inventory.

**Theorem 1.11 (zero Containing parameter equations).**

$$\forall (N j : \mathbb{N}) (y : \operatorname{Fin} (N + 1) \to \operatorname{Fin} 3) , (\operatorname{IsDeficit} y) \to (\exists i , y i = 0) \to ((\sum_{i : \operatorname{Fin} (N + 1)} (y i) . \operatorname{val}) = j) \to \operatorname{let} b := \operatorname{doubleTwoCount} y ; \operatorname{let} a := \operatorname{labelCount} y 2 - 2 * b ; N + 1 = \operatorname{labelCount} y 0 + \operatorname{labelCount} y 1 + a + 2 * b \land j = \operatorname{labelCount} y 1 + 2 * a + 4 * b \land a \leq j \land b \leq j$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ItalianDomination/RootedCycleGaps.zeroContaining_parameter_equations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

Removing the two twos in each exceptional gap leaves a isolated twos. The resulting label inventories determine the length and deficit equations and bound a and b by j.

**Theorem 1.12 (zero Containing all exceptional).**

$$\forall (N : \mathbb{N}) (y : \operatorname{Fin} (N + 1) \to \operatorname{Fin} 3) , (\operatorname{IsDeficit} y) \to (\exists i , y i = 0) \to (\operatorname{doubleTwoCount} y = \operatorname{labelCount} y 0) \to \operatorname{labelCount} y 1 = 0 \land \operatorname{labelCount} y 2 = 2 * \operatorname{doubleTwoCount} y$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ItalianDomination/RootedCycleGaps.zeroContaining_all_exceptional` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

When every zero gap is exceptional there are no ones and precisely two twos per exceptional gap.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/RootedCycleGaps.RefinedCycle`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/RootedCycleGaps.RootedRefinedCycle`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/RootedCycleGaps.ZeroFreeWords`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/RootedCycleGaps.labelCount_sum`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/RootedCycleGaps.refined_cycle_marking_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/RootedCycleGaps.rootedRefinedCycle_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/RootedCycleGaps.weight_eq_labelCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/RootedCycleGaps.zeroContaining_all_exceptional`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/RootedCycleGaps.zeroContaining_inventory_bounds`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/RootedCycleGaps.zeroContaining_parameter_equations`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/RootedCycleGaps.zeroFree_cycle_marking_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/RootedCycleGaps.zeroFree_twos_le_ones`
- Dependency: [D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords](OrdinaryWords.md)
