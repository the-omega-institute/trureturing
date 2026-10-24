# The exact component count of a strange quantum graph

## Abstract

Quantum graph components equal graph components plus loopless isolated strange edges.

Write Mat n for D5.S3.Quantum.Matrix.CfmRadialDerivative.Mat n, the complex square matrices indexed by Fin n. Write offDiag for D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment.offDiag, the complex linear map that sets the diagonal to zero. DFunLike.coe explicitly regards a linear map as a function. These notations give:

$$
\forall (n: \mathbb{N}), (\operatorname{Mat}\left(n\right) = \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right))
$$

$$
\forall (d: \mathbb{N}), (\forall (X: \operatorname{Mat}\left(d\right)), (\forall (i: \operatorname{Fin}\left(d\right)), (\forall (j: \operatorname{Fin}\left(d\right)), (\operatorname{DFunLike.coe}\left(\operatorname{offDiag}\right)\left(X, i, j\right) = \operatorname{ite}\left((i = j), (0: \mathbb{C}), X\left(i, j\right)\right)))))
$$

**Definition 1.1 (The realigned block matrix).**

$$\forall (n: \mathbb{N}), (\forall (A: \operatorname{Mat}\left(n\right)), (\forall (C: \operatorname{Mat}\left(n\right)), (\forall (d: (\operatorname{Fin}\left(n\right)) \to (\mathbb{C})), (\forall (p: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)), (\forall (q: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)), (\operatorname{realignedProjector}\left(A, C, d\right)\left(p, q\right) = \operatorname{ite}\left(((p).1 = (p).2), \operatorname{ite}\left((q = ((p).1, (p).1)), d\left((p).1\right), (0: \mathbb{C})\right), \operatorname{ite}\left((q = p), A\left((p).1, (p).2\right), \operatorname{ite}\left((q = ((p).2, (p).1)), C\left((p).1, (p).2\right), (0: \mathbb{C})\right)\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount.realignedProjector` (`✓ std3`).

*Citation.* Gian Luca Spitzer; Ion Nechita (2026). *Quantum Graph Theory by Example*. DOI: [10.22331/q-2026-10-06-2228](https://doi.org/10.22331/q-2026-10-06-2228). URL: <https://arxiv.org/abs/2603.23651v3>.

*Commentary.*

The matrix has the scalar d i on the coordinate (i,i). On the two coordinates (i,j) and (j,i), for distinct i and j, its block has first row (A i j, C i j) and second row (C j i, A j i); all other entries vanish. This is the direct sum in content/groupactions.tex, lines 172–177, with the trivial middle matrix specified in lines 246–249. The definition itself allows arbitrary A, C and d; self-adjointness and idempotence are separate hypotheses.

**Definition 1.2 (The adjacency operator by realignment).**

$$\forall (n: \mathbb{N}), (\forall (A: \operatorname{Mat}\left(n\right)), (\forall (C: \operatorname{Mat}\left(n\right)), (\forall (d: (\operatorname{Fin}\left(n\right)) \to (\mathbb{C})), ((\operatorname{adjacency}\left(A, C, d\right): (\operatorname{Mat}\left(n\right)) \to_{l[\mathbb{C}]} (\operatorname{Mat}\left(n\right))) = \operatorname{MatrixMap.of_{choi_{matrix}}}\left(\operatorname{realignedProjector}\left(A, C, d\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount.adjacency` (`✓ std3`).

*Citation.* Gian Luca Spitzer; Ion Nechita (2026). *Quantum Graph Theory by Example*. DOI: [10.22331/q-2026-10-06-2228](https://doi.org/10.22331/q-2026-10-06-2228). URL: <https://arxiv.org/abs/2603.23651v3>.

*Commentary.*

Here MatrixMap.of_choi_matrix denotes D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_choi_matrix. Nested subscripts in the displayed declaration name encode underscores. It converts the displayed matrix into a complex linear adjacency operator. Writing X^R for realignedProjector A C d and G for adjacency A C d, the realignment formula is (GZ)_{ik} = ∑_{j,l} X^R_{(i,j),(k,l)} Z_{jl}. In particular, the output indices are the first and third indices of the realigned matrix. Realignment and its projector characterization appear in content/prelims.tex, lines 170–177.

$$
\forall (n: \mathbb{N}), (\forall (A: \operatorname{Mat}\left(n\right)), (\forall (C: \operatorname{Mat}\left(n\right)), (\forall (d: (\operatorname{Fin}\left(n\right)) \to (\mathbb{C})), (\forall (Z: \operatorname{Mat}\left(n\right)), (\forall (i: \operatorname{Fin}\left(n\right)), (\forall (k: \operatorname{Fin}\left(n\right)), (\operatorname{DFunLike.coe}\left(\operatorname{adjacency}\left(A, C, d\right)\right)\left(Z, i, k\right) = \sum_{(j: \operatorname{Fin}\left(n\right))} (\sum_{(l: \operatorname{Fin}\left(n\right))} ((\operatorname{realignedProjector}\left(A, C, d\right)\left((i, j), (k, l)\right)) \cdot (Z\left(j, l\right)))))))))))
$$

**Definition 1.3 (A nonzero projection resolution).**

$$\forall (n: \mathbb{N}), (\forall (G: (\operatorname{Mat}\left(n\right)) \to_{l[\mathbb{C}]} (\operatorname{Mat}\left(n\right))), (\forall (k: \mathbb{N}), ((\operatorname{HasComponents}\left(G, k\right)) \Leftrightarrow (\exists (P: (\operatorname{Fin}\left(k\right)) \to (\operatorname{Mat}\left(n\right))), ((\forall (s: \operatorname{Fin}\left(k\right)), ((\operatorname{IsStarProjection}\left(P\left(s\right)\right)) \land (P\left(s\right) \ne (0: \operatorname{Mat}\left(n\right))))) \land ((\sum_{(s: \operatorname{Fin}\left(k\right))} (P\left(s\right)) = (1: \operatorname{Mat}\left(n\right))) \land (\forall (s: \operatorname{Fin}\left(k\right)), (\forall (t: \operatorname{Fin}\left(k\right)), ((s \ne t) \Rightarrow (\forall (Z: \operatorname{Mat}\left(n\right)), ((P\left(s\right)) \cdot (\operatorname{DFunLike.coe}\left(G\right)\left((P\left(t\right)) \cdot (Z)\right)) = (0: \operatorname{Mat}\left(n\right)))))))))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount.HasComponents` (`✓ std3`).

*Citation.* Gian Luca Spitzer; Ion Nechita (2026). *Quantum Graph Theory by Example*. DOI: [10.22331/q-2026-10-06-2228](https://doi.org/10.22331/q-2026-10-06-2228). URL: <https://arxiv.org/abs/2603.23651v3>.

*Commentary.*

A family indexed by Fin k consists of nonzero self-adjoint idempotent matrices summing to the identity. For distinct s and t, left multiplication by P s annihilates G applied after left multiplication by P t, on every matrix Z. This expresses at least k quantum connected components, as in content/prelims.tex, lines 253–259; content/graphtheory/conncomp.tex, lines 1–4, makes the nonzero requirement explicit. The formulation includes k = 0 and n = 0.

**Definition 1.4 (The underlying simple graph).**

$$\forall (n: \mathbb{N}), (\forall (A: \operatorname{Mat}\left(n\right)), (\forall (C: \operatorname{Mat}\left(n\right)), (\forall (i: \operatorname{Fin}\left(n\right)), (\forall (j: \operatorname{Fin}\left(n\right)), ((\operatorname{SimpleGraph.Adj}\left(\operatorname{underlyingGraph}\left(A, C\right), i, j\right)) \Leftrightarrow ((i \ne j) \land ((A\left(i, j\right) \ne (0: \mathbb{C})) \lor ((A\left(j, i\right) \ne (0: \mathbb{C})) \lor ((C\left(i, j\right) \ne (0: \mathbb{C})) \lor (C\left(j, i\right) \ne (0: \mathbb{C})))))))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount.underlyingGraph` (`✓ std3`).

*Citation.* Gian Luca Spitzer; Ion Nechita (2026). *Quantum Graph Theory by Example*. DOI: [10.22331/q-2026-10-06-2228](https://doi.org/10.22331/q-2026-10-06-2228). URL: <https://arxiv.org/abs/2603.23651v3>.

*Commentary.*

Two distinct vertices are adjacent exactly when at least one of the four entries of their off-diagonal block is nonzero. This relation is symmetric and excludes loops. Under the projector and undirectedness hypotheses, it forgets the edge types and phases of the strange graph in content/groupactions.tex, lines 408–427. Without those hypotheses it still defines the simple support graph of the four entries.

**Definition 1.5 (An isolated strange edge without endpoint loops).**

$$\forall (n: \mathbb{N}), (\forall (A: \operatorname{Mat}\left(n\right)), (\forall (C: \operatorname{Mat}\left(n\right)), (\forall (d: (\operatorname{Fin}\left(n\right)) \to (\mathbb{C})), (\forall (Q: \operatorname{SimpleGraph.ConnectedComponent}\left(\operatorname{underlyingGraph}\left(A, C\right)\right)), ((\operatorname{IsLoopFreeStrangeComponent}\left(A, C, d, Q\right)) \Leftrightarrow (\exists (i: \operatorname{Fin}\left(n\right)), (\exists (j: \operatorname{Fin}\left(n\right)), ((i \ne j) \land ((\operatorname{SimpleGraph.ConnectedComponent.supp}\left(Q\right) = \left\{i, j\right\}) \land ((\operatorname{SimpleGraph.Adj}\left(\operatorname{underlyingGraph}\left(A, C\right), i, j\right)) \land ((A\left(i, j\right) = \frac{(1: \mathbb{C})}{(2: \mathbb{C})}) \land ((d\left(i\right) = (0: \mathbb{C})) \land (d\left(j\right) = (0: \mathbb{C}))))))))))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount.IsLoopFreeStrangeComponent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gian Luca Spitzer; Ion Nechita (2026). *Quantum Graph Theory by Example*. DOI: [10.22331/q-2026-10-06-2228](https://doi.org/10.22331/q-2026-10-06-2228). URL: <https://arxiv.org/abs/2603.23651v3>.

*Commentary.*

This predicate is introduced here to state the exact component count. The support of Q must consist of exactly two distinct adjacent vertices i and j, with A i j = 1/2 and d i = d j = 0. Under the projector and undirectedness hypotheses, A i j = 1/2 identifies a strange edge, whose conjugate off-diagonal coefficients have product 1/4. The predicate places no restriction on its phase. It is a condition on a whole connected component, so the edge is isolated from all other vertices.

**Definition 1.6 (The classical component count).**

$$\forall (n: \mathbb{N}), (\forall (A: \operatorname{Mat}\left(n\right)), (\forall (C: \operatorname{Mat}\left(n\right)), ((\operatorname{graphComponentCount}\left(A, C\right): \mathbb{N}) = \operatorname{Fintype.card}\left(\operatorname{SimpleGraph.ConnectedComponent}\left(\operatorname{underlyingGraph}\left(A, C\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount.graphComponentCount` (`✓ std3`).

*Citation.* Gian Luca Spitzer; Ion Nechita (2026). *Quantum Graph Theory by Example*. DOI: [10.22331/q-2026-10-06-2228](https://doi.org/10.22331/q-2026-10-06-2228). URL: <https://arxiv.org/abs/2603.23651v3>.

*Commentary.*

This natural number is the cardinality of the connected-component type of the underlying simple graph, including isolated vertices. It is the classical count compared with the quantum count in content/graphtheory/conncomp.tex, lines 196–213 and 247–254. The cardinality is already a natural number; no scalar conversion is involved.

**Definition 1.7 (The exceptional component count).**

$$\forall (n: \mathbb{N}), (\forall (A: \operatorname{Mat}\left(n\right)), (\forall (C: \operatorname{Mat}\left(n\right)), (\forall (d: (\operatorname{Fin}\left(n\right)) \to (\mathbb{C})), ((\operatorname{loopFreeStrangeComponentCount}\left(A, C, d\right): \mathbb{N}) = \operatorname{Fintype.card}\left(\{Q: \operatorname{SimpleGraph.ConnectedComponent}\left(\operatorname{underlyingGraph}\left(A, C\right)\right) // \operatorname{IsLoopFreeStrangeComponent}\left(A, C, d, Q\right)\}\right)))))$$

*Formalization.* `D5/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount.loopFreeStrangeComponentCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gian Luca Spitzer; Ion Nechita (2026). *Quantum Graph Theory by Example*. DOI: [10.22331/q-2026-10-06-2228](https://doi.org/10.22331/q-2026-10-06-2228). URL: <https://arxiv.org/abs/2603.23651v3>.

*Commentary.*

This natural number is introduced here to state the exact component count. It counts precisely the connected components satisfying IsLoopFreeStrangeComponent. Each unordered two-vertex component is counted once, independently of the choice of its two endpoints. The subtype cardinality is a natural number, with no scalar conversion.

**Definition 1.8 (The exact-count assertion).**

$$(\operatorname{claim}) \Leftrightarrow (\forall (n: \mathbb{N}), (\forall (A: \operatorname{Mat}\left(n\right)), (\forall (C: \operatorname{Mat}\left(n\right)), (\forall (d: (\operatorname{Fin}\left(n\right)) \to (\mathbb{C})), ((\forall (i: \operatorname{Fin}\left(n\right)), (A\left(i, i\right) = d\left(i\right))) \Rightarrow ((\forall (i: \operatorname{Fin}\left(n\right)), (C\left(i, i\right) = d\left(i\right))) \Rightarrow ((\operatorname{IsHermitian}\left(\operatorname{realignedProjector}\left(A, C, d\right)\right)) \Rightarrow (((\operatorname{realignedProjector}\left(A, C, d\right)) \cdot (\operatorname{realignedProjector}\left(A, C, d\right)) = \operatorname{realignedProjector}\left(A, C, d\right)) \Rightarrow ((\operatorname{IsHermitian}\left(\operatorname{DFunLike.coe}\left(\operatorname{offDiag}\right)\left(A\right)\right)) \Rightarrow (\operatorname{IsGreatest}\left(\{(k: \mathbb{N}) \mid \operatorname{HasComponents}\left(\operatorname{adjacency}\left(A, C, d\right), k\right)\}, (\operatorname{graphComponentCount}\left(A, C\right)) + (\operatorname{loopFreeStrangeComponentCount}\left(A, C, d\right))\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gian Luca Spitzer; Ion Nechita (2026). *Quantum Graph Theory by Example*. DOI: [10.22331/q-2026-10-06-2228](https://doi.org/10.22331/q-2026-10-06-2228). URL: <https://arxiv.org/abs/2603.23651v3>.

*Commentary.*

The common diagonal conditions are A i i = d i and C i i = d i for every i. The realigned matrix is self-adjoint and idempotent, and offDiag A is self-adjoint. For every natural size n, the assertion says that the sum of the two displayed natural counts is both attainable as a quantum component count and an upper bound for all attainable counts. The question in content/conclusion.tex, line 8, asks for the exact count and the role of isolated strange edges of phase π; it does not give this formula. The asserted answer adds one for every isolated strange edge with zero endpoint diagonals, of any phase.

**Theorem 1.9 (The greatest attainable quantum component count).**

$$\forall (n: \mathbb{N}), (\forall (A: \operatorname{Mat}\left(n\right)), (\forall (C: \operatorname{Mat}\left(n\right)), (\forall (d: (\operatorname{Fin}\left(n\right)) \to (\mathbb{C})), ((\forall (i: \operatorname{Fin}\left(n\right)), (A\left(i, i\right) = d\left(i\right))) \Rightarrow ((\forall (i: \operatorname{Fin}\left(n\right)), (C\left(i, i\right) = d\left(i\right))) \Rightarrow ((\operatorname{IsHermitian}\left(\operatorname{realignedProjector}\left(A, C, d\right)\right)) \Rightarrow (((\operatorname{realignedProjector}\left(A, C, d\right)) \cdot (\operatorname{realignedProjector}\left(A, C, d\right)) = \operatorname{realignedProjector}\left(A, C, d\right)) \Rightarrow ((\operatorname{IsHermitian}\left(\operatorname{DFunLike.coe}\left(\operatorname{offDiag}\right)\left(A\right)\right)) \Rightarrow (\operatorname{IsGreatest}\left(\{(k: \mathbb{N}) \mid \operatorname{HasComponents}\left(\operatorname{adjacency}\left(A, C, d\right), k\right)\}, (\operatorname{graphComponentCount}\left(A, C\right)) + (\operatorname{loopFreeStrangeComponentCount}\left(A, C, d\right))\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount.result` (`✓ std3`). ∎

*Resolves.* `Problems/spitzer-nechita-2026-quantum-graph-component-count` (proved) by `D5/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"spitzer-nechita-2026-quantum-graph-component-count","declaration_gid":"D5/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Gian Luca Spitzer; Ion Nechita (2026). *Quantum Graph Theory by Example*. DOI: [10.22331/q-2026-10-06-2228](https://doi.org/10.22331/q-2026-10-06-2228). URL: <https://arxiv.org/abs/2603.23651v3>.

*Commentary.*

Fix n, A, C and d satisfying the five hypotheses. First examine a block indexed by distinct i and j. Self-adjointness gives A j i = A i j, conjugate(A i j) = A i j and C j i = conjugate(C i j). Idempotence gives (A i j)² + (C i j)(C j i) = A i j and (A i j)(C i j) + (C i j)(A j i) = C i j. Thus the block is zero, the identity, or a strange block with A i j = A j i = 1/2 and (C i j)(C j i) = 1/4. In particular A i j is nonzero on every edge.

For each pair q let K_q be the matrix whose (i,j) entry is X^R_{(i,j),q}. The diagonal matrices are K_(i,i) = d i E_ii, and for distinct i,j one has K_(i,j) = (A i j)E_ij + (C j i)E_ji. Commutation of a matrix P with every K_q forces P i i = P j j along each edge, hence along every path. For an edge i–j and a third vertex r, the same equations force P r i = 0. For distinct i and j they also give (P i j)(A j i) = (C i j)(P j i), and a nonzero P i j forces d i = d j = 0. If P is self-adjoint, i ≠ j, i has a neighbor and P i j is nonzero, then j is the only neighbor of i and i is the only neighbor of j. Their connected component is exactly {i,j}; the identity-block case would force P i j = 0, so this component is a loop-free isolated strange edge.

The projector identity for X^R yields G(Z) = ∑_q K_q Z K_qᴴ: the Choi matrix of this sum has entries ∑_r X^R_{p,r} conjugate(X^R_{q,r}) = X^R_{p,q}. A sum of matrices T_r T_rᴴ can vanish only when every T_r vanishes, since all its summands are positive semidefinite. Applying this fact to a projection resolution of the identity proves that its distinct members are orthogonal. For two self-adjoint projections P and Q, the identity P G(QZ) = 0 for every Z is equivalent to P K_q Q = 0 for every q: take Z = I, multiply on the right by P, and use the vanishing positive sum. Summing the cross terms against a resolution of I now shows that the separation conditions are equivalent to every projection commuting with every K_q. Orthogonality proves the converse.

To bound such a resolution, form W as the disjoint union of all connected components and the subtype of loop-free isolated strange components. Select one representative vertex of every component, and also the other vertex of each component in the subtype. These selected vertices are distinct, and |W| is graphComponentCount A C + loopFreeStrangeComponentCount A C d. They include every isolated vertex and both endpoints of every exceptional edge. Every omitted vertex therefore has a neighbor and belongs to a nonexceptional component. The preceding commutation equations force all off-diagonal entries incident to that vertex to vanish for every self-adjoint matrix in the commutant.

Compress each member P s of a resolution to the selected coordinates. The vanished entries show that compression preserves its square, so each compressed matrix is idempotent. It is nonzero: if it vanished, constancy of the diagonal on connected components would also kill every omitted diagonal entry, and the vanished off-diagonal entries would give P s = 0. The compressed matrices sum to the identity on the coordinate space W → ℂ. The bound for a sum of nonzero idempotent endomorphisms, D5.S3.Quantum.Matrix.RecordCapacity.card_le_finrank_of_idempotent_sum, therefore gives k ≤ dimℂ(W → ℂ) = |W|, which is the required upper bound.

For attainment, take the diagonal projection D_Q onto each connected component Q. These are nonzero self-adjoint projections summing to I and commuting with all K_q. Matrices K_(i,j) between different components vanish. On an exceptional component {i,j}, put b = C j i. The block equations give b conjugate(b) = 1/4. Algebraic closedness of ℂ supplies z with z² = 2b. Then (z conjugate(z))² = 1, and nonnegativity excludes the value −1, so z conjugate(z) = 1. Set D = E_ii + E_jj and H = conjugate(z)E_ij + z E_ji. Direct multiplication gives D² = D, DH = HD = H and H² = D; H is self-adjoint. Hence P = (D + H)/2 and R = D − P are nonzero self-adjoint projections, each with diagonal entries 1/2 at i and j, and P + R = D.

Here K_(i,j) = (z/2)H and K_(j,i) = K_(i,j)ᴴ, so P commutes with both. The two diagonal matrices K_(i,i) and K_(j,j) vanish because d i = d j = 0. Matrices between this pair and its complement vanish, while those supported in the complement multiply P to zero on either side. Thus P commutes with every K_q, and R does too, by subtracting P from D_Q. Replace D_Q by P and R on each exceptional component and retain D_Q on every other component. Indexing this family by W gives exactly graphComponentCount A C + loopFreeStrangeComponentCount A C d nonzero projections, still commuting with every K_q and still summing to I. Reindex by Fin of this natural number and use the separation equivalence to obtain an attainable quantum component count. Together with the upper bound, this proves it is the greatest attainable count. The construction uses no special phase, so every isolated strange edge with zero endpoint diagonals contributes two components, and every other graph component contributes one. If d vanishes everywhere, the correction counts all isolated strange edges.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount.HasComponents`
- Truth anchor: `D5/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount.IsLoopFreeStrangeComponent`
- Truth anchor: `D5/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount.adjacency`
- Truth anchor: `D5/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount.graphComponentCount`
- Truth anchor: `D5/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount.loopFreeStrangeComponentCount`
- Truth anchor: `D5/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount.realignedProjector`
- Truth anchor: `D5/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount.result`
- Truth anchor: `D5/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount.underlyingGraph`
- Dependency: [D5/S3/Quantum/Matrix/CfmRadialDerivative](CfmRadialDerivative.md)
- Dependency: [D5/S3/Quantum/Matrix/RecordCapacity](RecordCapacity.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/CoherenceBreakingAmendment](../QuantumChannels/CoherenceBreakingAmendment.md)
