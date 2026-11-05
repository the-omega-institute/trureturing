# Counting bubble eigenstate configurations

## Abstract

A marked-gap count gives the closed formula for labelled bubble configurations on a periodic chain.

**Definition 1.1 (Separated bubble centres).**

$$\forall (L: \mathbb{N}), (\forall (B: \operatorname{Finset}\left(\operatorname{Fin}\left(L\right)\right)), (\operatorname{D5.S3.Quantum.SpinChains.BubbleEigenstateDegeneracy.Admissible}\left(L, B\right) = (\forall (a: \operatorname{Fin}\left(L\right)), ((a \in B) \to (\forall (b: \operatorname{Fin}\left(L\right)), ((b \in B) \to ((a \ne b) \to (5 \le \operatorname{ite}\left(\operatorname{Fin.val}\left(a\right) < \operatorname{Fin.val}\left(b\right), (\operatorname{Fin.val}\left(b\right)) - (\operatorname{Fin.val}\left(a\right)), ((L) + (\operatorname{Fin.val}\left(b\right))) - (\operatorname{Fin.val}\left(a\right))\right)))))))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/BubbleEigenstateDegeneracy.Admissible` (`✓ std3`).

*Citation.* Bhaskar Mukherjee, Debasish Banerjee, K. Sengupta, Arnab Sen (2021). *Minimal model for Hilbert space fragmentation with local constraints*. DOI: [10.1103/PhysRevB.104.155117](https://doi.org/10.1103/PhysRevB.104.155117). URL: <https://arxiv.org/abs/2106.14897v3>.

*Commentary.*

The sites are Fin L, numbered from zero to L minus one. Admissible L B means that the clockwise distance from a to b is at least five for every ordered pair of distinct centres in B. Thus the condition holds in both directions. A three-site X or Y unit around each centre then leaves at least two down spins between units. This is the separation condition in fragmentation_prb_v2.tex, lines 645–647 and 670–674, of arXiv:2106.14897v3. Empty and singleton sets satisfy the pairwise condition; the counting formula below assumes L at least five.

**Definition 1.2 (The energy-resolved configuration count).**

$$\forall (L: \mathbb{N}), (\forall (E: \mathbb{Z}), ((\operatorname{D5.S3.Quantum.SpinChains.BubbleEigenstateDegeneracy.bubbleCount}\left(L, E\right): \mathbb{N}) = \sum_{(B: \operatorname{Finset}\left(\operatorname{Fin}\left(L\right)\right))\in\operatorname{Finset.filter}\left(\operatorname{D5.S3.Quantum.SpinChains.BubbleEigenstateDegeneracy.Admissible}\left(L\right), (\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(L\right)\right)\right))\right)} (\operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(\lambda (x: \operatorname{Finset}\left(\operatorname{Fin}\left(L\right)\right)) \mapsto (((2) \cdot ((\operatorname{Nat.cast}\left(\operatorname{Finset.card}\left(x\right)\right): \mathbb{Z}))) - ((\operatorname{Nat.cast}\left(\operatorname{Finset.card}\left(B\right)\right): \mathbb{Z})) = E), \operatorname{Finset.powerset}\left(B\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/BubbleEigenstateDegeneracy.bubbleCount` (`✓ std3`).

*Citation.* Bhaskar Mukherjee, Debasish Banerjee, K. Sengupta, Arnab Sen (2021). *Minimal model for Hilbert space fragmentation with local constraints*. DOI: [10.1103/PhysRevB.104.155117](https://doi.org/10.1103/PhysRevB.104.155117). URL: <https://arxiv.org/abs/2106.14897v3>.

*Commentary.*

For each admissible centre set B, a subset x of B specifies the centres labelled X; the remaining centres are labelled Y. Its energy is twice the cardinality of x minus the cardinality of B, evaluated in the integers. The outer sum counts these labellings over all centre sets, with translations counted separately. The empty set contributes the vacuum at energy zero. This is the source's counting definition in fragmentation_prb_v2.tex, lines 670–674; the energies of the X and Y units are described at lines 636–644. Nat.cast in the formulas explicitly embeds each natural cardinality into the integers.

**Definition 1.3 (The closed counting formula).**

$$\operatorname{D5.S3.Quantum.SpinChains.BubbleEigenstateDegeneracy.claim} = (\forall (L: \mathbb{N}), ((5 \le L) \to (\forall (E: \mathbb{Z}), ((\operatorname{Nat.cast}\left(\operatorname{D5.S3.Quantum.SpinChains.BubbleEigenstateDegeneracy.bubbleCount}\left(L, E\right)\right): \mathbb{Z}) = (\operatorname{ite}\left(E = 0, (1: \mathbb{Z}), (0: \mathbb{Z})\right)) + (\sum_{(n: \mathbb{N})\in\operatorname{Finset.Icc}\left(1, \operatorname{Nat.div}\left(L, 5\right)\right)} (((\operatorname{Nat.cast}\left(\operatorname{Nat.div}\left((L) \cdot (\operatorname{Nat.choose}\left(((L) - ((4) \cdot (n))) - (1), (n) - (1)\right)), n\right)\right): \mathbb{Z})) \cdot (\operatorname{ite}\left((\operatorname{Int.emod}\left(((\operatorname{Nat.cast}\left(n\right): \mathbb{Z})) + (E), 2\right) = 0) \land (\left|E\right| \le (\operatorname{Nat.cast}\left(n\right): \mathbb{Z})), (\operatorname{Nat.cast}\left(\operatorname{Nat.choose}\left(n, \operatorname{Int.toNat}\left(\operatorname{Int.ediv}\left(((\operatorname{Nat.cast}\left(n\right): \mathbb{Z})) + (E), 2\right)\right)\right)\right): \mathbb{Z}), (0: \mathbb{Z})\right))))))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/BubbleEigenstateDegeneracy.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bhaskar Mukherjee, Debasish Banerjee, K. Sengupta, Arnab Sen (2021). *Minimal model for Hilbert space fragmentation with local constraints*. DOI: [10.1103/PhysRevB.104.155117](https://doi.org/10.1103/PhysRevB.104.155117). URL: <https://arxiv.org/abs/2106.14897v3>.

*Commentary.*

For every natural chain length L at least five and every integer energy E, the count is the vacuum contribution plus a sum over positive bubble numbers n up to the natural quotient L / 5. Each summand is the number of n-centre sets times the number of labellings at energy E. The latter vanishes unless n + E is even and the absolute value of E is at most n. Nat.div denotes natural division, Int.ediv integer division, and Int.emod integer remainder; Int.toNat converts the nonnegative label index to a natural number. The source states that a closed form for arbitrary L was not found in fragmentation_prb_v2.tex, lines 729–731. This formula answers that counting question for labelled configurations. It does not assert the Hamiltonian eigenstate property or count the other eigenstates.

**Theorem 1.4 (The marked-gap enumeration).**

$$\forall (L: \mathbb{N}), ((5 \le L) \to (\forall (E: \mathbb{Z}), ((\operatorname{Nat.cast}\left(\operatorname{D5.S3.Quantum.SpinChains.BubbleEigenstateDegeneracy.bubbleCount}\left(L, E\right)\right): \mathbb{Z}) = (\operatorname{ite}\left(E = 0, (1: \mathbb{Z}), (0: \mathbb{Z})\right)) + (\sum_{(n: \mathbb{N})\in\operatorname{Finset.Icc}\left(1, \operatorname{Nat.div}\left(L, 5\right)\right)} (((\operatorname{Nat.cast}\left(\operatorname{Nat.div}\left((L) \cdot (\operatorname{Nat.choose}\left(((L) - ((4) \cdot (n))) - (1), (n) - (1)\right)), n\right)\right): \mathbb{Z})) \cdot (\operatorname{ite}\left((\operatorname{Int.emod}\left(((\operatorname{Nat.cast}\left(n\right): \mathbb{Z})) + (E), 2\right) = 0) \land (\left|E\right| \le (\operatorname{Nat.cast}\left(n\right): \mathbb{Z})), (\operatorname{Nat.cast}\left(\operatorname{Nat.choose}\left(n, \operatorname{Int.toNat}\left(\operatorname{Int.ediv}\left(((\operatorname{Nat.cast}\left(n\right): \mathbb{Z})) + (E), 2\right)\right)\right)\right): \mathbb{Z}), (0: \mathbb{Z})\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/BubbleEigenstateDegeneracy.result` (`✓ std3`). ∎

*Resolves.* `Problems/mukherjee-banerjee-sengupta-sen-2021-bubble-eigenstate-degeneracy` (proved) by `D5/S3/Quantum/SpinChains/BubbleEigenstateDegeneracy.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mukherjee-banerjee-sengupta-sen-2021-bubble-eigenstate-degeneracy","declaration_gid":"D5/S3/Quantum/SpinChains/BubbleEigenstateDegeneracy.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Bhaskar Mukherjee, Debasish Banerjee, K. Sengupta, Arnab Sen (2021). *Minimal model for Hilbert space fragmentation with local constraints*. DOI: [10.1103/PhysRevB.104.155117](https://doi.org/10.1103/PhysRevB.104.155117). URL: <https://arxiv.org/abs/2106.14897v3>.

*Commentary.*

First, an admissible set B occupies five disjoint clockwise sites per centre: send a centre and an offset in Fin 5 to their sum modulo L. Equality of two images with different centres would contradict one of the two directed separation inequalities. For equal centres the offsets are equal. This injection gives 5 times the cardinality of B at most L.

For a positive n with 5n at most L, consider boundary positions s₀ = 0, sₙ = L with successive differences at least five. Subtracting four from each successive difference gives n positive integers with sum L − 4n. Conversely, the partial sums of those integers plus four give the boundary positions. Successive differences recover every part, so these constructions are inverse. Clockwise separation can also be expressed by the natural representative of b − a in Fin L; this shows that translating all centres preserves admissibility.

The first n boundary positions form an admissible n-element set containing zero. Their strict increase proves the cardinality and the forward separation inequalities; the terminal boundary L gives the inequalities across zero. Equal such sets have equal increasing enumerations, hence equal partial sums and equal positive parts. Conversely, enumerate any admissible n-element set containing zero in increasing order and append L. Consecutive centres and the final gap to zero have separation at least five; when the only centre is zero, the final gap is L, at least five. The successive differences therefore recover a unique positive composition of L − 4n.

Now mark a centre a in a nonempty admissible set. Subtract a from every centre and use the preceding correspondence to obtain a positive composition. Conversely, translate the set constructed from a composition by a and mark a. The marked centre and increasing enumeration show that these operations are inverse. If c(L,n) denotes the number of admissible n-element sets, counting marked sets gives n c(L,n) on one side and L times the number of positive compositions on the other. Positive compositions of L − 4n into n parts number binomial(L − 4n − 1,n − 1). Thus n c(L,n) = L binomial(L − 4n − 1,n − 1), proving both the placement coefficient and the exactness of its natural division by n.

For a fixed centre set B of size n, a subset x of size k has energy 2k − n. Such subsets exist only when n + E is even and |E| is at most n. Under those conditions the energy equation is equivalent to k = Int.toNat((n + E) / 2); the subsets of that size number binomial(n,k). If either condition fails, the size bound k at most n contradicts the energy equation, so the filtered powerset is empty. At n = 0 the only centre set and its only subset are empty, giving one labelling exactly when E = 0.

Finally, group the defining sum by the cardinality n of B. The packing bound restricts n to zero through L / 5. Separate the zero term, and use the label count, which is constant over sets of the same size, to factor each positive-size sum. Cast this natural-number equality into the integers, distribute the cast over sums and products, and substitute the placement coefficient for every n from one through L / 5. This gives the displayed formula for every L at least five and every integer E.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/BubbleEigenstateDegeneracy.Admissible`
- Truth anchor: `D5/S3/Quantum/SpinChains/BubbleEigenstateDegeneracy.bubbleCount`
- Truth anchor: `D5/S3/Quantum/SpinChains/BubbleEigenstateDegeneracy.claim`
- Truth anchor: `D5/S3/Quantum/SpinChains/BubbleEigenstateDegeneracy.result`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraRunCompositions](../../Combinatorics/Geometry/MiuraRunCompositions.md)
