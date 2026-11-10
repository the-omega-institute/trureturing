# Reduction, vanishing criterion, and coarse determination of replica-three stabilizer multi-entropy

## Abstract

The replica-three multi-entropy of any normalized pure qubit stabilizer state reduces explicitly to its two- and three-party coarse-grainings, satisfies a refinement-weight vanishing criterion, and is determined across all nontrivial coarsenings by two- and three-party coarse data.

Combining the coarse-partition rank sum for replica-three stabilizer multi-entropies with the upper-sum inversion on the set-partition poset expresses S_3^{(q)} for every q >= 3 through two- and three-party coarse-grained multi-entropies with integer power scaling 3^{2 - q}, expands arbitrary linear combinations over nontrivial coarsenings as coarse-weighted rank sums, and shows that agreeing two- and three-party coarse data determine all coarse-grained replica-three multi-entropies even between states on different numbers of qubits. Akella and Gadde, arXiv:2610.27080v1 Section II Eqs. (7)-(9) and Appendix A, establish the underlying odd-replica graph-state rank formula whose n = 3 partition structure drives these linear relations.

**Theorem 1.1 (Explicit reduction of S_3^{(q)} to two- and three-party coarse-grained multi-entropies).**

$$\forall (N : \mathbb{N}), \forall (q : \mathbb{N}), 3 \leq q \Rightarrow (\forall (\psi : ((\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(2\right)) \to \mathbb{C})), ((\mathrm{StabilizedBy}\left(pauliSet, \psi\right)) \land (\sum_{(x : (\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(2\right)))} \left\lVert \psi(x) \right\rVert^{2} = 1)) \Rightarrow (\forall (col : (\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(q\right))), \mathrm{S}\left(3, q, col, \psi\right) = 3^{(2 - (q : \mathbb{Z}))} \cdot (\sum_{\pi \in \mathrm{partitionsOfCard}\left(q, 3\right)} 3 \cdot \mathrm{coarseMultiEntropy}\left(\pi, col, \psi\right) + \sum_{\sigma \in \mathrm{partitionsOfCard}\left(q, 2\right)} (3 - \sum_{B \in \mathrm{parts}\left(\sigma\right)} 2^{(\mathrm{card}\left(B\right) - 1)}) \cdot \mathrm{coarseMultiEntropy}\left(\sigma, col, \psi\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/StabilizerMultiEntropyReplicaThree.replica_three_two_and_three_party_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

For any q >= 3, normalized pure qubit stabilizer state psi, and colouring col : Fin N to Fin q, passing to a graph form Gamma writes 3 coarseMultiEntropy(pi, col, psi) = (log 2 / 2) upperRankSum(r, pi) on Pi_3(q) and coarseMultiEntropy(sigma, col, psi) = (log 2 / 2) upperRankSum(r, sigma) on Pi_2(q), where r(tau) = partitionRank(Gamma, col, tau). Applying coarse_upper_sum_reduction_and_triangular_inversion cancels the S(|X|, 2) + S(|Y|, 2) = 2^{|X|-1} + 2^{|Y|-1} - 2 three-block refinements of each two-block partition sigma = {X, Y} against coefficient 3 - 2^{|X|-1} - 2^{|Y|-1} and multiplies by 3^{2 - q} = (3^{q - 2})^{-1} to recover S(3, q, col, psi).

For small party counts the reduction specializes directly. When q = 3, every two-block partition sigma in Pi_2(3) has block sizes 2 and 1, so 3 - 2^{2-1} - 2^{1-1} = 3 - 2 - 1 = 0 and 3^{2 - 3} * 3 S_3^{(3)}(bot) = S_3^{(3)}. When q = 4, the four singleton cuts with block sizes 3 and 1 carry coefficient 3 - 2^2 - 2^0 = -2, while the three balanced cuts with block sizes 2 and 2 carry coefficient 3 - 2^1 - 2^1 = -1, giving S_3^{(4)} = (1/9)[3 sum_{pi in Pi_3(4)} S_3^{(3)}(pi) - 2 sum_{|X|=1} S_3^{(2)}({X, Y}) - sum_{|X|=|Y|=2} S_3^{(2)}({X, Y})].

**Theorem 1.2 (Coarse-weight rank expansion and sufficient vanishing criterion for linear combinations).**

$$\forall (q : \mathbb{N}), 2 \leq q \Rightarrow (\forall (c : (\mathrm{PartyPartition}\left(q\right) \to \mathbb{R})), (\forall (N : \mathbb{N}), \forall (\Gamma : \mathrm{Matrix}\left(\mathrm{Fin}\left(N\right), \mathrm{Fin}\left(N\right), \mathrm{ZMod}\left(2\right)\right)), \forall (\psi : ((\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(2\right)) \to \mathbb{C})), \mathrm{IsGraphFormOf}\left(\Gamma, \psi\right) \Rightarrow (\forall (col : (\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(q\right))), \sum_{\rho \in \mathrm{nontrivialPartitions}\left(q\right)} c(\rho) \cdot \mathrm{coarseMultiEntropy}\left(\rho, col, \psi\right) = \frac{\mathrm{log}\left(2\right)}{2} \cdot \sum_{\sigma \in \mathrm{twoOrThreePartitions}\left(q\right)} \mathrm{coarseWeight}\left(c, \sigma\right) \cdot \mathrm{partitionRank}\left(\Gamma, col, \sigma\right))) \land ((\forall (\sigma : \mathrm{PartyPartition}\left(q\right)), \sigma \in \mathrm{twoOrThreePartitions}\left(q\right) \Rightarrow (\mathrm{coarseWeight}\left(c, \sigma\right) = 0)) \Rightarrow (\forall (N : \mathbb{N}), \forall (\psi : ((\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(2\right)) \to \mathbb{C})), ((\mathrm{StabilizedBy}\left(pauliSet, \psi\right)) \land (\sum_{(x : (\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(2\right)))} \left\lVert \psi(x) \right\rVert^{2} = 1)) \Rightarrow (\forall (col : (\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(q\right))), \sum_{\rho \in \mathrm{nontrivialPartitions}\left(q\right)} c(\rho) \cdot \mathrm{coarseMultiEntropy}\left(\rho, col, \psi\right) = 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/StabilizerMultiEntropyReplicaThree.coarse_linear_combination_and_vanishing_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

For q >= 2 and any real coefficient family c on partitions of Fin q, rewriting coarseMultiEntropy(rho, col, psi) = (log 2 / 2) * 3^{2 - |rho|} upperRankSum(r, rho) for |rho| >= 2 and exchanging summation over rho <= sigma equates sum_{|rho| >= 2} c(rho) coarseMultiEntropy(rho, col, psi) on every graph form Gamma of psi to (log 2 / 2) sum_{sigma in Pi_2(q) cup Pi_3(q)} coarseWeight(c, sigma) partitionRank(Gamma, col, sigma). Consequently, if coarseWeight(c, sigma) = 0 for all sigma in Pi_2(q) cup Pi_3(q), the linear combination vanishes identically across all qubit counts N, all normalized pure qubit stabilizer states, and all colourings into Fin q.

For four parties (q = 4), Akella, Iizuka and Miyata, arXiv:2607.06050v1 Section II Eq. (5), define GM_3^{(4)} = S_3^{(4)} - (1/3) sum_{pi in Pi_3(4)} S_3^{(3)}(pi) + (1/3) sum_{|X|=1} S_3^{(2)}({X, Y}) - a I_3 with I_3 = sum_{|X|=1} S_3^{(2)}({X, Y}) - sum_{|X|=|Y|=2} S_3^{(2)}({X, Y}). Setting L = GM_3^{(4)} + (a - 1/9) I_3 assigns c(bot) = 1 (scaled by 3^{-2} = 1/9), c(pi) = -1/3 on Pi_3(4) (scaled by 3^{-1} = 1/3), c(sigma) = 2/9 on singleton cuts |X| = 1, and c(sigma) = 1/9 on balanced cuts |X| = |Y| = 2. Then coarseWeight(c, pi) = 1/9 - (1/3)(1/3) = 0 on Pi_3(4); each singleton cut refines from bot, three three-block partitions, and itself, giving 1/9 - 3(1/9) + 2/9 = 0; and each balanced cut refines from bot, two three-block partitions, and itself, giving 1/9 - 2(1/9) + 1/9 = 0. The vanishing criterion therefore yields GM_3^{(4)} = -(a - 1/9) I_3 for all normalized pure qubit stabilizer states, matching StabilizerMultiEntropyCollapse.result.

**Theorem 1.3 (Two- and three-party coarse data determine all replica-three multi-entropies).**

$$\forall (N : \mathbb{N}), \forall (M : \mathbb{N}), \forall (q : \mathbb{N}), 2 \leq q \Rightarrow (\forall (\psi : ((\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(2\right)) \to \mathbb{C})), \forall (\phi : ((\mathrm{Fin}\left(M\right) \to \mathrm{Fin}\left(2\right)) \to \mathbb{C})), (((\mathrm{StabilizedBy}\left(pauliSet, \psi\right)) \land (\sum_{(x : (\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(2\right)))} \left\lVert \psi(x) \right\rVert^{2} = 1)) \land ((\mathrm{StabilizedBy}\left(pauliSet, \phi\right)) \land (\sum_{(x : (\mathrm{Fin}\left(M\right) \to \mathrm{Fin}\left(2\right)))} \left\lVert \phi(x) \right\rVert^{2} = 1))) \Rightarrow (\forall (col : (\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(q\right))), \forall (colB : (\mathrm{Fin}\left(M\right) \to \mathrm{Fin}\left(q\right))), ((\forall (\sigma : \mathrm{PartyPartition}\left(q\right)), \sigma \in \mathrm{partitionsOfCard}\left(q, 2\right) \Rightarrow (\mathrm{coarseMultiEntropy}\left(\sigma, col, \psi\right) = \mathrm{coarseMultiEntropy}\left(\sigma, colB, \phi\right))) \land (\forall (\pi : \mathrm{PartyPartition}\left(q\right)), \pi \in \mathrm{partitionsOfCard}\left(q, 3\right) \Rightarrow (\mathrm{coarseMultiEntropy}\left(\pi, col, \psi\right) = \mathrm{coarseMultiEntropy}\left(\pi, colB, \phi\right)))) \Rightarrow ((\forall (\rho : \mathrm{PartyPartition}\left(q\right)), \rho \in \mathrm{nontrivialPartitions}\left(q\right) \Rightarrow (\mathrm{coarseMultiEntropy}\left(\rho, col, \psi\right) = \mathrm{coarseMultiEntropy}\left(\rho, colB, \phi\right))) \land (\mathrm{S}\left(3, q, col, \psi\right) = \mathrm{S}\left(3, q, colB, \phi\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/StabilizerMultiEntropyReplicaThree.coarse_two_three_data_determine_replica_three_multi_entropies` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

Given normalized pure qubit stabilizer states psi on N qubits and psiPrime on NPrime qubits with colourings col : Fin N to Fin q and colPrime : Fin NPrime to Fin q (q >= 2), choose graph forms Gamma and GammaPrime. Because (log 2 / 2) * 3^{2 - k} != 0, equality of coarseMultiEntropy on Pi_2(q) and Pi_3(q) forces matching upper sums upperRankSum(r, sigma) = upperRankSum(rPrime, sigma) on Pi_2(q) and Pi_3(q). Triangular determination in coarse_upper_sum_reduction_and_triangular_inversion then equates upperRankSum(r, rho) = upperRankSum(rPrime, rho) for every partition rho, so coarseMultiEntropy(rho, col, psi) = coarseMultiEntropy(rho, colPrime, psiPrime) whenever |rho| >= 2, and evaluating at rho = bot equates S(3, q, col, psi) = S(3, q, colPrime, psiPrime).

Scope and open boundary: all results here hold for normalized pure qubit stabilizer states at replica index n = 3 under the anchored replica convention; other replica indices n != 3, qudit stabilizer states, mixed states, and non-stabilizer states are outside scope, and no definition of genuine multi-entropy for q >= 5 is fixed. The vanishing criterion is proved in the sufficient direction only: because coarseWeight : c mapsto w is surjective by triangular back-substitution on twoOrThreePartitions(q), vanishing of L across all stabilizer states and colourings forces w_sigma = 0 for all sigma in Pi_2(q) cup Pi_3(q) if and only if the rank functionals (psi, col) mapsto partitionRank(Gamma, col, sigma) are linearly independent over normalized pure qubit stabilizer states, which remains an open question.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/StabilizerMultiEntropyReplicaThree.coarse_linear_combination_and_vanishing_criterion`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/StabilizerMultiEntropyReplicaThree.coarse_two_three_data_determine_replica_three_multi_entropies`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/StabilizerMultiEntropyReplicaThree.replica_three_two_and_three_party_reduction`
- Dependency: [D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement](../../../Combinatorics/Partitions/CoarseThreeBlockRefinement.md)
- Dependency: [D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphFormReplicaThreeRank](GraphFormReplicaThreeRank.md)
- Dependency: [D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse](../StabilizerMultiEntropyCollapse.md)
