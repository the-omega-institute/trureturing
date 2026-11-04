# Replica-three stabilizer multi-entropy via graph forms and coarse party partitions

## Abstract

Every normalized pure qubit stabilizer state admits a graph form on which opposite nonzero ternary replica characters biject onto two- and three-block party partitions, expressing the replica-three multi-entropy and its coarse-grainings as sums of masked F2 adjacency ranks.

Following the replica convention of Gadde, Krishna and Sharma, Phys. Rev. D 106, 126001, in the anchored form of Akella, Iizuka and Miyata, arXiv:2607.06050v1 Appendix A, a q-party pure N-qubit state psi with colouring col : Fin N to Fin q (allowing empty parties) is contracted over replicas r in (Z/3Z)^{q-1}, with the last party q - 1 acting by the identity. By Van den Nest, Dehaene and De Moor, Phys. Rev. A 69, 022316, and Schlingemann, Quantum Inf. Comput. 2, 307-323, every normalized pure qubit stabilizer state is local-unitary equivalent up to a unit phase to a graph state |Gamma>. Akella and Gadde, arXiv:2610.27080v1 Section II Eqs. (7)-(9) and Appendix A, give an odd-replica rank formula for graph states whose n = 3 specialization groups nonzero F4 labels by equality partition; retaining the factor n^{-(q-2)} yields the coarse-partition rank sum proved below.

**Definition 1.1 (Normalized N-qubit graph state).**

$$\forall (N : \mathbb{N}), \forall (\Gamma : \mathrm{Matrix}\left(\mathrm{Fin}\left(N\right), \mathrm{Fin}\left(N\right), \mathrm{ZMod}\left(2\right)\right)), \mathrm{graphState}\left(\Gamma\right) = (2^{-\frac{(N : \mathbb{R})}{2}} : \mathbb{C}) \cdot \mathrm{graphAmp}\left(\Gamma\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphFormReplicaThreeRank.graphState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* M. Van den Nest, J. Dehaene, B. De Moor (2004). *Graphical description of the action of local Clifford transformations on graph states*. DOI: [10.1103/PhysRevA.69.022316](https://doi.org/10.1103/PhysRevA.69.022316). URL: <https://arxiv.org/abs/quant-ph/0308151v2>.

*Commentary.*

Scales the unnormalized binary quadratic phase vector graphAmp(Gamma) by 2^{-N/2} so that |Gamma> has unit Hilbert norm.

**Definition 1.2 (Graph form of a pure qubit state).**

$$\forall (N : \mathbb{N}), \forall (\Gamma : \mathrm{Matrix}\left(\mathrm{Fin}\left(N\right), \mathrm{Fin}\left(N\right), \mathrm{ZMod}\left(2\right)\right)), \forall (\psi : ((\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(2\right)) \to \mathbb{C})), \mathrm{IsGraphFormOf}\left(\Gamma, \psi\right) \Leftrightarrow ((\mathrm{IsSymm}\left(\Gamma\right)) \land (\forall (u : \mathrm{Fin}\left(N\right)), \Gamma(u, u) = 0) \land (\exists (U : (\mathrm{Fin}\left(N\right) \to \mathrm{Matrix}\left(\mathrm{Fin}\left(2\right), \mathrm{Fin}\left(2\right), \mathbb{C}\right))), \exists (\lambda : \mathbb{C}), (\forall (u : \mathrm{Fin}\left(N\right)), U(u) \in \mathrm{unitaryGroup}\left(\mathrm{Fin}\left(2\right), \mathbb{C}\right)) \land (\left\lVert \lambda \right\rVert = 1) \land (\psi = \lambda \cdot \mathrm{mulVec}\left(\mathrm{tensorOp}\left(U\right), \mathrm{graphState}\left(\Gamma\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphFormReplicaThreeRank.IsGraphFormOf` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* M. Van den Nest, J. Dehaene, B. De Moor (2004). *Graphical description of the action of local Clifford transformations on graph states*. DOI: [10.1103/PhysRevA.69.022316](https://doi.org/10.1103/PhysRevA.69.022316). URL: <https://arxiv.org/abs/quant-ph/0308151v2>.

*Commentary.*

Asserts that Gamma is symmetric over ZMod 2 with zero diagonal and that psi equals lambda * (U_0 x ... x U_{N-1}) |Gamma> for single-qubit unitaries U(u) and a scalar lambda with ||lambda|| = 1.

**Definition 1.3 (Anchored party translation vector).**

$$\forall (q : \mathbb{N}), \forall (c : \mathrm{Fin}\left(q\right)), \forall (i : \mathrm{Fin}\left((q - 1)\right)), \mathrm{partyDelta}\left(c, i\right) = \mathrm{ite}\left((i : \mathbb{N}) = (c : \mathbb{N}), 1, 0\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphFormReplicaThreeRank.partyDelta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

Assigns the c-th standard basis vector of (Z/3Z)^{q-1} to party c < q - 1 and the zero vector to the last party q - 1.

**Definition 1.4 (Party evaluation of a ternary character).**

$$\forall (q : \mathbb{N}), \forall (t : (\mathrm{Fin}\left((q - 1)\right) \to \mathrm{ZMod}\left(3\right))), \forall (c : \mathrm{Fin}\left(q\right)), \mathrm{charEval}\left(t, c\right) = \sum_{(i : \mathrm{Fin}\left((q - 1)\right))} t(i) \cdot \mathrm{partyDelta}\left(c, i\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphFormReplicaThreeRank.charEval` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

Evaluates f_t(c) = t . delta_c in Z/3Z, taking value t_c for c < q - 1 and 0 on the last party q - 1.

**Definition 1.5 (Fibre partition of a ternary character).**

$$\forall (q : \mathbb{N}), \forall (t : (\mathrm{Fin}\left((q - 1)\right) \to \mathrm{ZMod}\left(3\right))), \mathrm{charPartition}\left(t\right) = \mathrm{ofSetoid}\left(\mathrm{ker}\left(\mathrm{charEval}\left(t\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphFormReplicaThreeRank.charPartition` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

Partitions Fin q into the nonempty fibres of charEval(t).

**Definition 1.6 (Coarse-grained replica-three multi-entropy).**

$$\forall (N : \mathbb{N}), \forall (q : \mathbb{N}), \forall (\pi : \mathrm{PartyPartition}\left(q\right)), \forall (col : (\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(q\right))), \forall (\psi : ((\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(2\right)) \to \mathbb{C})), \mathrm{coarseMultiEntropy}\left(\pi, col, \psi\right) = \mathrm{S}\left(3, \mathrm{card}\left(\mathrm{parts}\left(\pi\right)\right), \mathrm{coarseCol}\left(\pi, \mathrm{symm}\left(\mathrm{equivFin}\left(\mathrm{parts}\left(\pi\right)\right)\right), col\right), \psi\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphFormReplicaThreeRank.coarseMultiEntropy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

Evaluates S_3^{(|pi|)} on psi under the coarse-grained colouring induced by the canonical block enumeration of pi.

**Theorem 1.7 (Unit replica-one contraction, graph-form existence, and replica-three rank contraction).**

$$(\forall (N : \mathbb{N}), \forall (q : \mathbb{N}), \forall (col : (\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(q\right))), \forall (\psi : ((\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(2\right)) \to \mathbb{C})), \sum_{(x : (\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(2\right)))} \left\lVert \psi(x) \right\rVert^{2} = 1 \Rightarrow (\mathrm{Z}\left(1, q, col, \psi\right) = 1)) \land (\forall (N : \mathbb{N}), \forall (\psi : ((\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(2\right)) \to \mathbb{C})), ((\mathrm{StabilizedBy}\left(pauliSet, \psi\right)) \land (\sum_{(x : (\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(2\right)))} \left\lVert \psi(x) \right\rVert^{2} = 1)) \Rightarrow (\exists (\Gamma : \mathrm{Matrix}\left(\mathrm{Fin}\left(N\right), \mathrm{Fin}\left(N\right), \mathrm{ZMod}\left(2\right)\right)), \mathrm{IsGraphFormOf}\left(\Gamma, \psi\right))) \land (\forall (N : \mathbb{N}), \forall (q : \mathbb{N}), \forall (\Gamma : \mathrm{Matrix}\left(\mathrm{Fin}\left(N\right), \mathrm{Fin}\left(N\right), \mathrm{ZMod}\left(2\right)\right)), \forall (\psi : ((\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(2\right)) \to \mathbb{C})), \mathrm{IsGraphFormOf}\left(\Gamma, \psi\right) \Rightarrow (\forall (col : (\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(q\right))), \forall (P : \mathrm{Finset}\left((\mathrm{Fin}\left((q - 1)\right) \to \mathrm{ZMod}\left(3\right))\right)), ((\neg(0 \in P)) \land (\forall (t : (\mathrm{Fin}\left((q - 1)\right) \to \mathrm{ZMod}\left(3\right))), t \neq 0 \Rightarrow (t \in P \Leftrightarrow \neg(-t \in P)))) \Rightarrow ((\sum_{(x : (\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(2\right)))} \left\lVert \psi(x) \right\rVert^{2} = 1) \land (0 < \mathrm{Re}\left(\mathrm{Z}\left(3, q, col, \psi\right)\right)) \land (\mathrm{Im}\left(\mathrm{Z}\left(3, q, col, \psi\right)\right) = 0) \land (\mathrm{Z}\left(3, q, col, \psi\right) = (2^{\sum_{t \in P} \mathrm{rank}\left(\mathrm{C}\left(\Gamma, \mathrm{delta}\left(col\right), t\right)\right)})^{-1}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphFormReplicaThreeRank.graph_form_existence_and_replica_rank_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

Shows that Z(1, q, col, psi) = 1 whenever sum_x ||psi(x)||^2 = 1; extracts a symmetric zero-diagonal graph form Gamma for every normalized pure qubit stabilizer state by factoring the reciprocal norm 2^{-N/2} out of the stabilizer normal-form scalar; and proves for every graph form Gamma of psi and every opposite-pair representative set P in (Z/3Z)^{q-1} that psi has unit norm and Z(3, q, col, psi) is a positive real number equal to 2^{-sum_{t in P} rank C(Gamma, delta(col), t)}.

**Theorem 1.8 (Bijection of opposite ternary characters onto coarse partitions and the partition-rank sum for S_3^{(q)}).**

$$(\forall (q : \mathbb{N}), \forall (t : (\mathrm{Fin}\left((q - 1)\right) \to \mathrm{ZMod}\left(3\right))), \mathrm{charPartition}\left(-t\right) = \mathrm{charPartition}\left(t\right)) \land (\forall (q : \mathbb{N}), 2 \leq q \Rightarrow (\forall (P : \mathrm{Finset}\left((\mathrm{Fin}\left((q - 1)\right) \to \mathrm{ZMod}\left(3\right))\right)), ((\neg(0 \in P)) \land (\forall (t : (\mathrm{Fin}\left((q - 1)\right) \to \mathrm{ZMod}\left(3\right))), t \neq 0 \Rightarrow (t \in P \Leftrightarrow \neg(-t \in P)))) \Rightarrow ((\mathrm{BijOn}\left(charPartition, P, \mathrm{twoOrThreePartitions}\left(q\right)\right)) \land ((\mathrm{card}\left(P\right) : \mathbb{R}) = \frac{((3 : \mathbb{R})^{(q - 1)} - 1)}{2}) \land (\frac{((3 : \mathbb{R})^{(q - 1)} - 1)}{2} = (\mathrm{stirlingSecond}\left(q, 2\right) : \mathbb{R}) + (\mathrm{stirlingSecond}\left(q, 3\right) : \mathbb{R}))))) \land (\forall (N : \mathbb{N}), \forall (q : \mathbb{N}), 2 \leq q \Rightarrow (\forall (\Gamma : \mathrm{Matrix}\left(\mathrm{Fin}\left(N\right), \mathrm{Fin}\left(N\right), \mathrm{ZMod}\left(2\right)\right)), \forall (\psi : ((\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(2\right)) \to \mathbb{C})), \mathrm{IsGraphFormOf}\left(\Gamma, \psi\right) \Rightarrow (\forall (col : (\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(q\right))), \mathrm{S}\left(3, q, col, \psi\right) = \frac{\mathrm{log}\left(2\right)}{2 \cdot 3^{(q - 2)}} \cdot \sum_{\pi \in \mathrm{twoOrThreePartitions}\left(q\right)} \mathrm{partitionRank}\left(\Gamma, col, \pi\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphFormReplicaThreeRank.replica_three_coarse_partition_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

Because negation is a bijection of Z/3Z, charEval(-t) = -charEval(t) has the same fibres as charEval(t), giving charPartition(-t) = charPartition(t). For q >= 2 and nonzero t, charEval(t) vanishes at q - 1 and takes at least one nonzero value in Z/3Z, so charPartition(t) has two or three blocks. Identifying Fin q with Option(Fin(q - 1)) reduces injectivity on P to TernaryPartitionOrbit, while assigning 0 to the block of q - 1 and injective values in {1, 2} to the remaining one or two blocks proves surjectivity onto twoOrThreePartitions(q). Counting both sides yields (3^{q-1} - 1)/2 = S(q, 2) + S(q, 3), and C(Gamma, delta(col), t) coincides entrywise with maskedAdj(Gamma, col, charPartition(t)), transforming the replica rank sum into (log 2 / (2 * 3^{q-2})) sum_{pi in Pi_2(q) cup Pi_3(q)} partitionRank(Gamma, col, pi).

**Theorem 1.9 (Party-permutation invariance, coarse-graining upper sum, and bipartite off-diagonal rank formula).**

$$(\forall (N : \mathbb{N}), \forall (q : \mathbb{N}), 2 \leq q \Rightarrow (\forall (\psi : ((\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(2\right)) \to \mathbb{C})), ((\mathrm{StabilizedBy}\left(pauliSet, \psi\right)) \land (\sum_{(x : (\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(2\right)))} \left\lVert \psi(x) \right\rVert^{2} = 1)) \Rightarrow (\forall (col : (\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(q\right))), \forall (\tau : \mathrm{Perm}\left(\mathrm{Fin}\left(q\right)\right)), \mathrm{S}\left(3, q, \tau \circ col, \psi\right) = \mathrm{S}\left(3, q, col, \psi\right)))) \land (\forall (N : \mathbb{N}), \forall (q : \mathbb{N}), \forall (k : \mathbb{N}), \forall (\Gamma : \mathrm{Matrix}\left(\mathrm{Fin}\left(N\right), \mathrm{Fin}\left(N\right), \mathrm{ZMod}\left(2\right)\right)), \forall (\psi : ((\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(2\right)) \to \mathbb{C})), \mathrm{IsGraphFormOf}\left(\Gamma, \psi\right) \Rightarrow (\forall (col : (\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(q\right))), \forall (\pi : \mathrm{PartyPartition}\left(q\right)), 2 \leq \mathrm{card}\left(\mathrm{parts}\left(\pi\right)\right) \Rightarrow (\forall (B : \mathrm{Equiv}\left(\mathrm{Fin}\left(k\right), \mathrm{parts}\left(\pi\right)\right)), (\mathrm{S}\left(3, k, \mathrm{coarseCol}\left(\pi, B, col\right), \psi\right) = \mathrm{coarseMultiEntropy}\left(\pi, col, \psi\right)) \land (\mathrm{coarseMultiEntropy}\left(\pi, col, \psi\right) = \frac{\mathrm{log}\left(2\right)}{2 \cdot 3^{(\mathrm{card}\left(\mathrm{parts}\left(\pi\right)\right) - 2)}} \cdot \sum_{\sigma \in \mathrm{twoOrThreePartitions}\left(q\right) \land (\pi \leq \sigma)} \mathrm{partitionRank}\left(\Gamma, col, \sigma\right))))) \land (\forall (N : \mathbb{N}), \forall (q : \mathbb{N}), 2 \leq q \Rightarrow (\forall (\psi : ((\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(2\right)) \to \mathbb{C})), ((\mathrm{StabilizedBy}\left(pauliSet, \psi\right)) \land (\sum_{(x : (\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(2\right)))} \left\lVert \psi(x) \right\rVert^{2} = 1)) \Rightarrow (\forall (col : (\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(q\right))), \mathrm{coarseMultiEntropy}\left((\mathrm{bot} : \mathrm{PartyPartition}\left(q\right)), col, \psi\right) = \mathrm{S}\left(3, q, col, \psi\right)))) \land (\forall (N : \mathbb{N}), \forall (q : \mathbb{N}), \forall (\Gamma : \mathrm{Matrix}\left(\mathrm{Fin}\left(N\right), \mathrm{Fin}\left(N\right), \mathrm{ZMod}\left(2\right)\right)), \forall (\psi : ((\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(2\right)) \to \mathbb{C})), \mathrm{IsGraphFormOf}\left(\Gamma, \psi\right) \Rightarrow (\forall (col : (\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(q\right))), \forall (\sigma : \mathrm{PartyPartition}\left(q\right)), \sigma \in \mathrm{partitionsOfCard}\left(q, 2\right) \Rightarrow (\forall (X : \mathrm{Finset}\left(\mathrm{Fin}\left(q\right)\right)), \forall (Y : \mathrm{Finset}\left(\mathrm{Fin}\left(q\right)\right)), ((\mathrm{parts}\left(\sigma\right) = \mathrm{pair}\left(X, Y\right)) \land (X \neq Y)) \Rightarrow (\mathrm{coarseMultiEntropy}\left(\sigma, col, \psi\right) = \mathrm{log}\left(2\right) \cdot \mathrm{rank}\left(\mathrm{offDiagBlock}\left(\Gamma, col, X, Y\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphFormReplicaThreeRank.party_symmetry_coarse_graining_and_bipartite_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

Pulling partitions back along a surjective party map m : Fin q to Fin k bijects twoOrThreePartitions(k) onto the two- and three-block partitions sigma >= ker(m) while preserving maskedAdj and partitionRank. When m is a permutation tau of Fin q, ker(tau) is the discrete partition bot, proving S(3, q, tau o col, psi) = S(3, q, col, psi). When m comes from any block listing B : Fin k to pi.parts with |pi| >= 2, ker(m) = pi, proving block-order independence S(3, k, coarseCol(pi, B, col), psi) = coarseMultiEntropy(pi, col, psi), recovery coarseMultiEntropy(bot, col, psi) = S(3, q, col, psi), and the upper-sum formula (log 2 / (2 * 3^{|pi|-2})) sum_{sigma >= pi} partitionRank(Gamma, col, sigma). For a two-block partition sigma = {X, Y}, sigma is maximal in twoOrThreePartitions(q) and bipartite_masked_antidiagonal_rank gives partitionRank(Gamma, col, sigma) = 2 rank(offDiagBlock(Gamma, col, X, Y)), so coarseMultiEntropy(sigma, col, psi) = log 2 * rank(Gamma_{X,Y}).

For a two-block partition sigma = {X, Y}, the identity S_3^{(2)}(sigma) = log 2 * rank_{F2}(Gamma_{X,Y}) matches the bipartite Renyi entanglement entropy of a graph state established by Hein, Eisert and Briegel, Phys. Rev. A 69, 062311. As an explicit three-party illustration, for the three-qubit chain graph state with adjacency edges (0, 1) and (1, 2) and one qubit per party (q = 3, col = id), the three two-block partitions {01, 2}, {02, 1}, {12, 0} and the single three-block partition {0, 1, 2} each produce a masked 3 x 3 binary matrix of rank 2; the coarse-partition sum therefore gives S_3^{(3)} = (log 2 / (2 * 3^1)) * (2 + 2 + 2 + 2) = (4/3) log 2, matching the chain formula (1 + 1/n) log 2 at n = 3 in Czech, Feng, Wu and Xie, arXiv:2606.06582v2 Appendix B Eq. (B.9).

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphFormReplicaThreeRank.IsGraphFormOf`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphFormReplicaThreeRank.charEval`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphFormReplicaThreeRank.charPartition`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphFormReplicaThreeRank.coarseMultiEntropy`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphFormReplicaThreeRank.graphState`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphFormReplicaThreeRank.graph_form_existence_and_replica_rank_formula`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphFormReplicaThreeRank.partyDelta`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphFormReplicaThreeRank.party_symmetry_coarse_graining_and_bipartite_entropy`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphFormReplicaThreeRank.replica_three_coarse_partition_sum`
- Dependency: [D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement](../../../Combinatorics/Partitions/CoarseThreeBlockRefinement.md)
- Dependency: [D5/S3/Combinatorics/Partitions/TernaryPartitionOrbit](../../../Combinatorics/Partitions/TernaryPartitionOrbit.md)
- Dependency: [D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse](../StabilizerMultiEntropyCollapse.md)
