# A finite counterexample to improved thermal recall convergence

## Abstract

Removing intermediate memory resets increases the permutation approximation error in a finite reduced protocol.

The system has d levels and the memory has n levels. Joint states are real-valued functions on Fin d × Fin n. The source defines the two-level thermalisation in TR.tex lines 269–275, the sequential rounds and truncated protocol in lines 289–296, the memory reset in lines 305–312, and the composed protocols in lines 315–324. At infinite temperature each elementary step is the average of the two selected entries, and the memory starts uniformly.

**Definition 1.1 (Two-level averaging).**

$$\forall d \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall a \in \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(n\right),\; \forall b \in \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(n\right),\; \forall v \in \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(n\right) \to \mathbb{R},\; \forall x \in \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(n\right),\; \operatorname{average}\left(a, b, v\right)\left(x\right) = \operatorname{if} ((x = a) \lor (x = b)) \operatorname{then} \frac{(v\left(a\right) + v\left(b\right))}{2} \operatorname{else} v\left(x\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ThermalRecallTruncationRefutation.average` (`✓ std3`).

*Citation.* Jakub Czartowski; A. de Oliveira Junior; Kamil Korzekwa (2023). *Thermal Recall: Memory-Assisted Markovian Thermal Processes*. DOI: [10.1103/PRXQuantum.4.040304](https://doi.org/10.1103/PRXQuantum.4.040304). URL: <https://arxiv.org/abs/2303.12840v2>.

*Commentary.*

At infinite temperature, replace the values at two joint states a and b by their average and leave every other value unchanged. This is the infinite-temperature form of the source's two-level thermalisation (TR.tex lines 269–275).

**Definition 1.2 (A sequential thermalisation block).**

$$\forall d \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(d\right),\; \forall j \in \operatorname{Fin}\left(d\right),\; \forall v \in \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(n\right) \to \mathbb{R},\; \operatorname{block}\left(n, i, j, v\right) = \operatorname{List}.\operatorname{foldl}\left(\operatorname{fun} (u: \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(n\right) \to \mathbb{R}) \mapsto (\operatorname{fun} (k: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{List}.\operatorname{foldl}\left(\operatorname{fun} (u: \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(n\right) \to \mathbb{R}) \mapsto (\operatorname{fun} (l: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{average}\left((i, k), (j, l), u\right))), u, \operatorname{List}.\operatorname{finRange}\left(n\right)\right))), v, \operatorname{List}.\operatorname{finRange}\left(n\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ThermalRecallTruncationRefutation.block` (`✓ std3`).

*Citation.* Jakub Czartowski; A. de Oliveira Junior; Kamil Korzekwa (2023). *Thermal Recall: Memory-Assisted Markovian Thermal Processes*. DOI: [10.1103/PRXQuantum.4.040304](https://doi.org/10.1103/PRXQuantum.4.040304). URL: <https://arxiv.org/abs/2303.12840v2>.

*Commentary.*

For a transposition of system levels i and j, process every memory level k of i in increasing order; for each k, average it successively with every memory level l of j in increasing order. The nested list folds implement the N rounds and the N steps in each round described in TR.tex lines 289–296.

**Definition 1.3 (A system state with uniform memory).**

$$\forall d \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall p \in \operatorname{Fin}\left(d\right) \to \mathbb{R},\; \operatorname{joint}\left(n, p\right) = \operatorname{mixtureJoint}\left(p\right)\left(\operatorname{Function}.\operatorname{const}\left(\operatorname{Fin}\left(d\right), \operatorname{Function}.\operatorname{const}\left(\operatorname{Fin}\left(n\right), ((n : \mathbb{R}))^{-1}\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ThermalRecallTruncationRefutation.joint` (`✓ std3`).

*Citation.* Jakub Czartowski; A. de Oliveira Junior; Kamil Korzekwa (2023). *Thermal Recall: Memory-Assisted Markovian Thermal Processes*. DOI: [10.1103/PRXQuantum.4.040304](https://doi.org/10.1103/PRXQuantum.4.040304). URL: <https://arxiv.org/abs/2303.12840v2>.

*Commentary.*

Couple a system population p to a uniform memory. Each joint entry is p at its system level multiplied by the inverse of the real memory dimension, matching the infinite-temperature memory state in TR.tex lines 289–291 and 338.

**Definition 1.4 (Memory reset).**

$$\forall d \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall v \in \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(n\right) \to \mathbb{R},\; \operatorname{reset}\left(v\right) = \operatorname{joint}\left(n, \operatorname{marginal}\left(v\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ThermalRecallTruncationRefutation.reset` (`✓ std3`).

*Citation.* Jakub Czartowski; A. de Oliveira Junior; Kamil Korzekwa (2023). *Thermal Recall: Memory-Assisted Markovian Thermal Processes*. DOI: [10.1103/PRXQuantum.4.040304](https://doi.org/10.1103/PRXQuantum.4.040304). URL: <https://arxiv.org/abs/2303.12840v2>.

*Commentary.*

Sum a joint state over the memory coordinate to obtain the system marginal, then tensor that marginal with a uniform memory. This is the full memory thermalisation from TR.tex lines 305–308.

**Definition 1.5 (Output without intermediate resets).**

$$\forall d \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall p \in \operatorname{Fin}\left(d\right) \to \mathbb{R},\; \forall w \in \operatorname{List}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)\right),\; \operatorname{truncatedOutput}\left(n, p, w\right) = \operatorname{marginal}\left(\operatorname{List}.\operatorname{foldl}\left(\operatorname{fun} (v: \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(n\right) \to \mathbb{R}) \mapsto (\operatorname{fun} (z: \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)) \mapsto (\operatorname{block}\left(n, z.1, z.2\right)\left(v\right))), \operatorname{joint}\left(n, p\right), w\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ThermalRecallTruncationRefutation.truncatedOutput` (`✓ std3`).

*Citation.* Jakub Czartowski; A. de Oliveira Junior; Kamil Korzekwa (2023). *Thermal Recall: Memory-Assisted Markovian Thermal Processes*. DOI: [10.1103/PRXQuantum.4.040304](https://doi.org/10.1103/PRXQuantum.4.040304). URL: <https://arxiv.org/abs/2303.12840v2>.

*Commentary.*

Start from the joint state and apply the blocks in the word successively, with no reset between blocks. Return the system marginal, corresponding to the truncated composite protocol in TR.tex lines 293–296 and 321–322.

**Definition 1.6 (Output with intermediate resets).**

$$\forall d \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall p \in \operatorname{Fin}\left(d\right) \to \mathbb{R},\; \forall w \in \operatorname{List}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)\right),\; \operatorname{resetOutput}\left(n, p, w\right) = \operatorname{marginal}\left(\operatorname{List}.\operatorname{foldl}\left(\operatorname{fun} (v: \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(n\right) \to \mathbb{R}) \mapsto (\operatorname{fun} (z: \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)) \mapsto (\operatorname{reset}\left(\operatorname{block}\left(n, z.1, z.2\right)\left(v\right)\right))), \operatorname{joint}\left(n, p\right), w\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ThermalRecallTruncationRefutation.resetOutput` (`✓ std3`).

*Citation.* Jakub Czartowski; A. de Oliveira Junior; Kamil Korzekwa (2023). *Thermal Recall: Memory-Assisted Markovian Thermal Processes*. DOI: [10.1103/PRXQuantum.4.040304](https://doi.org/10.1103/PRXQuantum.4.040304). URL: <https://arxiv.org/abs/2303.12840v2>.

*Commentary.*

Start from the joint state and apply each block followed immediately by a memory reset. Return the final system marginal, corresponding to the reset protocol in TR.tex lines 309–322.

**Definition 1.7 (Reduced neighbour word).**

$$\forall d \in \mathbb{N},\; \forall p \in \operatorname{Fin}\left(d\right) \to \mathbb{R},\; \forall w \in \operatorname{List}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)\right),\; \operatorname{IsReducedNeighbourWord}\left(p, w\right) \Leftrightarrow (\forall n \in \mathbb{N},\; (n < \operatorname{List}.\operatorname{length}\left(w\right)) \Rightarrow (\operatorname{let} z = w[n]; \operatorname{let} r = \operatorname{applySwaps}\left(p, \operatorname{List}.\operatorname{take}\left(n, w\right)\right); (z.1 < z.2) \land ((r\left(z.2\right) < r\left(z.1\right)) \land (\forall c \in \operatorname{Fin}\left(d\right),\; \neg ((r\left(z.2\right) < r\left(c\right)) \land (r\left(c\right) < r\left(z.1\right)))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/ThermalRecallTruncationRefutation.IsReducedNeighbourWord` (`✓ std3`).

*Citation.* Jakub Czartowski; A. de Oliveira Junior; Kamil Korzekwa (2023). *Thermal Recall: Memory-Assisted Markovian Thermal Processes*. DOI: [10.1103/PRXQuantum.4.040304](https://doi.org/10.1103/PRXQuantum.4.040304). URL: <https://arxiv.org/abs/2303.12840v2>.

*Commentary.*

A word is reduced and neighbour-admissible when every position exchanges an increasing pair of system indices that is adjacent in the current population order and whose two values remain in their original relative order. The current order is obtained by applying the preceding swaps to p. This formalizes the reduced neighbour-transposition condition in TR.tex lines 315–325.

**Definition 1.8 (Improved convergence for reduced words).**

$$\operatorname{claim} \Leftrightarrow (\forall d \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall p \in \operatorname{Fin}\left(d\right) \to \mathbb{R},\; \forall w \in \operatorname{List}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)\right),\; (0 < n) \Rightarrow ((\forall i \in \operatorname{Fin}\left(d\right),\; 0 \le p\left(i\right)) \Rightarrow ((\sum_{i: \operatorname{Fin}\left(d\right)} (p\left(i\right)) = (1 : \mathbb{R})) \Rightarrow ((\operatorname{StrictAnti}\left(p\right)) \Rightarrow ((\operatorname{IsReducedNeighbourWord}\left(p, w\right)) \Rightarrow (\operatorname{totalVariation}\left(\operatorname{applySwaps}\left(p, w\right), \operatorname{truncatedOutput}\left(n, p, w\right)\right) \le \operatorname{totalVariation}\left(\operatorname{applySwaps}\left(p, w\right), \operatorname{resetOutput}\left(n, p, w\right)\right)))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/ThermalRecallTruncationRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jakub Czartowski; A. de Oliveira Junior; Kamil Korzekwa (2023). *Thermal Recall: Memory-Assisted Markovian Thermal Processes*. DOI: [10.1103/PRXQuantum.4.040304](https://doi.org/10.1103/PRXQuantum.4.040304). URL: <https://arxiv.org/abs/2303.12840v2>.

*Commentary.*

For every positive memory dimension, nonnegative system population of total mass one, strictly decreasing population, and reduced neighbour word, the total variation distance from the ideal swapped population is no larger without intermediate resets than with them. This is the repository's formal reading of the improved-convergence conjecture stated in TR.tex lines 417–427.

**Theorem 1.9 (A four-level counterexample).**

$$\neg (\operatorname{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/ThermalRecallTruncationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/czartowski-deoliveirajunior-korzekwa-2023-thermal-recall-truncation` (refuted) by `D5/S3/StatisticalMechanics/ThermalRecallTruncationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"czartowski-deoliveirajunior-korzekwa-2023-thermal-recall-truncation","declaration_gid":"D5/S3/StatisticalMechanics/ThermalRecallTruncationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jakub Czartowski; A. de Oliveira Junior; Kamil Korzekwa (2023). *Thermal Recall: Memory-Assisted Markovian Thermal Processes*. DOI: [10.1103/PRXQuantum.4.040304](https://doi.org/10.1103/PRXQuantum.4.040304). URL: <https://arxiv.org/abs/2303.12840v2>.

*Commentary.*

Use four system levels, two memory levels, the strictly decreasing probability vector (1/2, 1/4, 2/9, 1/36), and the word ((0,1),(2,3),(0,3)). The three swaps are adjacent in the successive orders 0123, 1023, 1032, so the word satisfies the reduced-neighbour condition.

The probability and strict-order hypotheses follow by checking the four coordinates. Evaluating the three blocks gives the ideal population (2/9, 1/2, 1/36, 1/4), the truncated output (31/144, 13/32, 29/288, 5/18), and the reset output (2/9, 13/32, 29/288, 13/48).

The exact finite sums defining total variation then give the identity that the distance to the truncated output equals the distance to the reset output plus 1/144. Applying the claimed inequality to this instance contradicts that positive gap, so the universal claim is false.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/ThermalRecallTruncationRefutation.IsReducedNeighbourWord`
- Truth anchor: `D5/S3/StatisticalMechanics/ThermalRecallTruncationRefutation.average`
- Truth anchor: `D5/S3/StatisticalMechanics/ThermalRecallTruncationRefutation.block`
- Truth anchor: `D5/S3/StatisticalMechanics/ThermalRecallTruncationRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/ThermalRecallTruncationRefutation.joint`
- Truth anchor: `D5/S3/StatisticalMechanics/ThermalRecallTruncationRefutation.reset`
- Truth anchor: `D5/S3/StatisticalMechanics/ThermalRecallTruncationRefutation.resetOutput`
- Truth anchor: `D5/S3/StatisticalMechanics/ThermalRecallTruncationRefutation.result`
- Truth anchor: `D5/S3/StatisticalMechanics/ThermalRecallTruncationRefutation.truncatedOutput`
- Dependency: [D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy](../Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.md)
- Dependency: [D5/S3/Entropy/Mixing/MixtureEntropyBracket](../Entropy/Mixing/MixtureEntropyBracket.md)
- Dependency: [D5/S3/TotalVariation/CycleSingleCutMinimax](../TotalVariation/CycleSingleCutMinimax.md)
