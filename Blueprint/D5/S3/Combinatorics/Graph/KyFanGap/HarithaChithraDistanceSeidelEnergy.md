# Distance Seidel energy after deleting an edge

## Abstract

Deleting any edge of a complete bipartite graph with both parts of size at least two strictly increases its distance Seidel energy for the matrix J - I - 2D.

**Definition 1.1 (Distance Seidel matrix).**

$$\forall (V : Type), [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall (G : \operatorname{SimpleGraph}\left(V\right)), \operatorname{distSeidel}\left(G\right) = \operatorname{Matrix.of}\left(\operatorname{fun} (u : V) \mapsto \operatorname{fun} (v : V) \mapsto 1 - \operatorname{ite}\left((u = v), 1, 0\right) - 2 \cdot (\operatorname{SimpleGraph.dist}\left(G, u, v\right) : \mathbb{R})\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/KyFanGap/HarithaChithraDistanceSeidelEnergy.distSeidel` (`✓ std3`).

*Citation.* T. Haritha and A. V. Chithra (2022). *Distance Seidel matrix of a connected graph*. DOI: [10.1080/09728600.2025.2479147](https://doi.org/10.1080/09728600.2025.2479147). URL: <https://arxiv.org/abs/2210.05940v2>.

*Commentary.*

Page 2: "D^S(G) = J − I − 2D = −1 if v_r is adjacent to v_t, 1 − 2d_G(v_r, v_t) otherwise." The displayed expression encodes J − I − 2D entrywise using SimpleGraph.dist, with zero diagonal. The source's casewise expression instead gives diagonal one. Only the matrix equation is used here. On the complete bipartite graphs and their single-edge deletions considered below, every pair is connected.

**Definition 1.2 (Energy from characteristic roots).**

$$\forall (V : Type), [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall (M : \operatorname{Matrix}\left(V, V, \mathbb{R}\right)), \operatorname{energy}\left(M\right) = \operatorname{Multiset.sum}\left(\operatorname{Multiset.map}\left(\operatorname{fun} (x : \mathbb{R}) \mapsto \lvert x\rvert, \operatorname{Polynomial.roots}\left(\operatorname{Matrix.charpoly}\left(M\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/KyFanGap/HarithaChithraDistanceSeidelEnergy.energy` (`✓ std3`).

*Citation.* T. Haritha and A. V. Chithra (2022). *Distance Seidel matrix of a connected graph*. DOI: [10.1080/09728600.2025.2479147](https://doi.org/10.1080/09728600.2025.2479147). URL: <https://arxiv.org/abs/2210.05940v2>.

*Commentary.*

Page 2: "The distance Seidel energy E_{D^S}(G) of a graph G is defined as E_{D^S}(G) = Σ_{r=1}^n |∂_r^S|." Matrix.charpoly and Polynomial.roots retain multiplicity. For a real symmetric matrix the characteristic polynomial splits over the reals, so this sum is the sum of absolute eigenvalues. For a general real matrix the expression sums only its real characteristic roots; the theorem applies it only to symmetric matrices.

**Definition 1.3 (Problem 5.1).**

$$\operatorname{claim} = (\forall (a : \mathbb{N}), \forall (b : \mathbb{N}), (2 \le a) \Rightarrow ((2 \le b) \Rightarrow (\forall (e : \operatorname{Sym2}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right)\right)\right)), (e \in \operatorname{SimpleGraph.edgeSet}\left(\operatorname{completeBipartiteGraph}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right)\right)\right)) \Rightarrow (\operatorname{energy}\left(\operatorname{distSeidel}\left(\operatorname{completeBipartiteGraph}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right)\right)\right)\right) < \operatorname{energy}\left(\operatorname{distSeidel}\left(\operatorname{SimpleGraph.deleteEdges}\left(\operatorname{completeBipartiteGraph}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right)\right), \{e\}\right)\right)\right)))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/KyFanGap/HarithaChithraDistanceSeidelEnergy.claim` (`✓ std3`).

*Citation.* T. Haritha and A. V. Chithra (2022). *Distance Seidel matrix of a connected graph*. DOI: [10.1080/09728600.2025.2479147](https://doi.org/10.1080/09728600.2025.2479147). URL: <https://arxiv.org/abs/2210.05940v2>.

*Commentary.*

Problem 5.1, page 13: "Let G = K_{a,b}, with a, b > 1. Is E_{D^S}(K_{a,b} − e) > E_{D^S}(K_{a,b}), for any edge e of K_{a,b}?" The proposition gives the affirmative universal statement. The vertex type is Fin a ⊕ Fin b; edges are unordered pairs in the edge set. The natural-number inequalities 2 ≤ a and 2 ≤ b express a, b > 1. SimpleGraph.deleteEdges removes the singleton edge set.

**Theorem 1.4 (Strict increase for every edge).**

$$\forall (a : \mathbb{N}), \forall (b : \mathbb{N}), (2 \le a) \Rightarrow ((2 \le b) \Rightarrow (\forall (e : \operatorname{Sym2}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right)\right)\right)), (e \in \operatorname{SimpleGraph.edgeSet}\left(\operatorname{completeBipartiteGraph}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right)\right)\right)) \Rightarrow (\operatorname{energy}\left(\operatorname{distSeidel}\left(\operatorname{completeBipartiteGraph}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right)\right)\right)\right) < \operatorname{energy}\left(\operatorname{distSeidel}\left(\operatorname{SimpleGraph.deleteEdges}\left(\operatorname{completeBipartiteGraph}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right)\right), \{e\}\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/KyFanGap/HarithaChithraDistanceSeidelEnergy.result` (`✓ std3`). ∎

*Resolves.* `Problems/haritha-chithra-2022-distance-seidel-energy-problem-5-1` (proved) by `D5/S3/Combinatorics/Graph/KyFanGap/HarithaChithraDistanceSeidelEnergy.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"haritha-chithra-2022-distance-seidel-energy-problem-5-1","declaration_gid":"D5/S3/Combinatorics/Graph/KyFanGap/HarithaChithraDistanceSeidelEnergy.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* T. Haritha and A. V. Chithra (2022). *Distance Seidel matrix of a connected graph*. DOI: [10.1080/09728600.2025.2479147](https://doi.org/10.1080/09728600.2025.2479147). URL: <https://arxiv.org/abs/2210.05940v2>.

*Commentary.*

The distance Seidel matrix of the complete bipartite graph has energy 6(a+b−2). Its sign is a symmetric involution which reflects the two part-indicator directions. Deleting an edge changes only the two corresponding off-diagonal entries, each by −4. This preserves the supporting trace functional. Equality in the trace bound for the sum of absolute eigenvalues would force commutation with the involution, whereas a commutator entry is 8/a at another vertex of the first part. Since a ≥ 2, that entry is nonzero and the energy inequality is strict. The proof treats every a,b ≥ 2, including the cases a = 2 and a = 3 of Propositions 5.2–5.3. It makes no universal assertion about the alternative diagonal-one matrix.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/HarithaChithraDistanceSeidelEnergy.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/HarithaChithraDistanceSeidelEnergy.distSeidel`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/HarithaChithraDistanceSeidelEnergy.energy`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/HarithaChithraDistanceSeidelEnergy.result`
