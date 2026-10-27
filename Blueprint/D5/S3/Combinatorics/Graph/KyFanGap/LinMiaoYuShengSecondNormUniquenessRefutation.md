# Second-norm equality does not determine the graph

## Abstract

Two nonisomorphic connected graphs on six vertices and seven edges have the same second Ky Fan norm of their LI-matrices.

**Definition 1.1 (Centered Laplacian).**

$$\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{LI}\left(G\right) = \operatorname{letI} : \operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right) := \operatorname{Classical}.\operatorname{decRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right); \operatorname{SimpleGraph}.\operatorname{lapMatrix}\left(\mathrm{Real}, G\right) - (\frac{2 \cdot (\operatorname{Nat}.\operatorname{card}\left(\operatorname{SimpleGraph}.\operatorname{edgeSet}\left(G\right)\right) : \mathrm{Real})}{(n : \mathrm{Real})}) \cdot (1 : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathrm{Real}\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/KyFanGap/LinMiaoYuShengSecondNormUniquenessRefutation.LI` (`✓ std3`).

*Citation.* Zhen Lin, Lianying Miao, Guanglong Yu and Han Sheng (2022). *On the Ky Fan k-norm of the LI-matrix of graphs*. DOI: [10.13001/ela.2022.5943](https://doi.org/10.13001/ela.2022.5943). URL: <https://arxiv.org/abs/2012.11162v2>.

*Commentary.*

The introduction, journal page 681, states: “Let G be a graph with n vertices and m edges. Then the LI-matrix of G is defined as LI(G)=L(G)−(2m/n)Iₙ.” Here SimpleGraph.lapMatrix is the degree diagonal matrix minus the adjacency matrix, and Nat.card G.edgeSet counts unordered edges. The quotient is in ℝ. Classical.decRel supplies the adjacency decision procedure.

**Definition 1.2 (The graph with triangles on a common edge).**

$$\forall n \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \operatorname{Gmn}\left(n, m\right) = \operatorname{SimpleGraph}.\operatorname{fromRel}\left(\operatorname{fun} u : \operatorname{Fin}\left(n\right) \mapsto \operatorname{fun} v : \operatorname{Fin}\left(n\right) \mapsto (\operatorname{val}\left(u\right) = 0) \lor ((\operatorname{val}\left(u\right) = 1) \land ((2 \le \operatorname{val}\left(v\right)) \land (\operatorname{val}\left(v\right) < \operatorname{Nat}.\operatorname{sub}\left(m, n\right) + 3)))\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/KyFanGap/LinMiaoYuShengSecondNormUniquenessRefutation.Gmn` (`✓ std3`).

*Citation.* Zhen Lin, Lianying Miao, Guanglong Yu and Han Sheng (2022). *On the Ky Fan k-norm of the LI-matrix of graphs*. DOI: [10.13001/ela.2022.5943](https://doi.org/10.13001/ela.2022.5943). URL: <https://arxiv.org/abs/2012.11162v2>.

*Commentary.*

Section 2 of arXiv v2 (journal page 682) states: “The Gₘ,ₙ, shown in Fig. 2.1, is a graph with n vertices and m edges which has m−n+1 triangles with a common edge and 2n−m+3 pendent edges incident with one end vertex of the common edge.” The printed pendant count conflicts with the stated order and size. On the conjecture's range n ≤ m and m+3 ≤ 2n, the graph drawn there has 2n−m−3 pendant vertices: vertex 0 is universal, and vertex 1 meets vertices 2 through m−n+2. Gmn takes n first and m second. SimpleGraph.fromRel removes loops and symmetrizes the displayed relation; Nat.sub is truncated subtraction.

**Definition 1.3 (Conjecture 5.11 with separate maxima).**

$$\operatorname{claim} = (\forall n \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; (n \le m) \Rightarrow ((m + 3 \le 2 \cdot n) \Rightarrow (\forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; (\operatorname{SimpleGraph}.\operatorname{Connected}\left(G\right)) \Rightarrow ((\operatorname{Nat}.\operatorname{card}\left(\operatorname{SimpleGraph}.\operatorname{edgeSet}\left(G\right)\right) = m) \Rightarrow (\forall k \in \mathrm{Nat},\; ((k = 2) \lor (k = 3)) \Rightarrow ((\operatorname{kyFan}\left(k, \operatorname{LI}\left(G\right)\right) \le \operatorname{kyFan}\left(k, \operatorname{LI}\left(\operatorname{Gmn}\left(n, m\right)\right)\right)) \land ((\operatorname{kyFan}\left(k, \operatorname{LI}\left(G\right)\right) = \operatorname{kyFan}\left(k, \operatorname{LI}\left(\operatorname{Gmn}\left(n, m\right)\right)\right)) \Leftrightarrow (\operatorname{Nonempty}\left(\operatorname{SimpleGraph}.\operatorname{Iso}\left(G, \operatorname{Gmn}\left(n, m\right)\right)\right)))))))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/KyFanGap/LinMiaoYuShengSecondNormUniquenessRefutation.claim` (`✓ std3`).

*Citation.* Zhen Lin, Lianying Miao, Guanglong Yu and Han Sheng (2022). *On the Ky Fan k-norm of the LI-matrix of graphs*. DOI: [10.13001/ela.2022.5943](https://doi.org/10.13001/ela.2022.5943). URL: <https://arxiv.org/abs/2012.11162v2>.

*Commentary.*

Conjecture 5.11, journal page 694, states: “Among all connected graphs with n and m edges n ≤ m ≤ 2n−3, the Gₘ,ₙ is the unique graph with maximal value of ‖LI(G)‖F₂ and ‖LI(G)‖F₃.” The phrase “with n and m edges” means n vertices and m edges. The proposition asserts the maximum and equality characterization separately for k=2 and k=3, on Fin n. The upper range is m+3 ≤ 2n. The existing kyFan sums singular values in decreasing order with multiplicity and zero extension. Graph isomorphism is expressed by Nonempty (G ≃g Gmn n m). A simultaneous-maximizer interpretation is outside this proposition.

**Theorem 1.4 (A second-norm tie without isomorphism).**

$$\neg (\forall n \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; (n \le m) \Rightarrow ((m + 3 \le 2 \cdot n) \Rightarrow (\forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; (\operatorname{SimpleGraph}.\operatorname{Connected}\left(G\right)) \Rightarrow ((\operatorname{Nat}.\operatorname{card}\left(\operatorname{SimpleGraph}.\operatorname{edgeSet}\left(G\right)\right) = m) \Rightarrow (\forall k \in \mathrm{Nat},\; ((k = 2) \lor (k = 3)) \Rightarrow ((\operatorname{kyFan}\left(k, \operatorname{LI}\left(G\right)\right) \le \operatorname{kyFan}\left(k, \operatorname{LI}\left(\operatorname{Gmn}\left(n, m\right)\right)\right)) \land ((\operatorname{kyFan}\left(k, \operatorname{LI}\left(G\right)\right) = \operatorname{kyFan}\left(k, \operatorname{LI}\left(\operatorname{Gmn}\left(n, m\right)\right)\right)) \Leftrightarrow (\operatorname{Nonempty}\left(\operatorname{SimpleGraph}.\operatorname{Iso}\left(G, \operatorname{Gmn}\left(n, m\right)\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/KyFanGap/LinMiaoYuShengSecondNormUniquenessRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/lmys511-kyfan` (refuted) by `D5/S3/Combinatorics/Graph/KyFanGap/LinMiaoYuShengSecondNormUniquenessRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lmys511-kyfan","declaration_gid":"D5/S3/Combinatorics/Graph/KyFanGap/LinMiaoYuShengSecondNormUniquenessRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Zhen Lin, Lianying Miao, Guanglong Yu and Han Sheng (2022). *On the Ky Fan k-norm of the LI-matrix of graphs*. DOI: [10.13001/ela.2022.5943](https://doi.org/10.13001/ela.2022.5943). URL: <https://arxiv.org/abs/2012.11162v2>.

*Commentary.*

On Fin 6, take all edges {0,i} for 1 ≤ i ≤ 5 and the additional edges {1,2}, {3,4}. This graph is connected and has seven edges. Its degrees are 5,2,2,2,2,1, whereas Gmn 6 7 has degrees 5,3,2,2,1,1, so the graphs are nonisomorphic. Their Laplacian spectra are respectively {6,3,3,1,1,0} and {6,4,2,1,1,0}. Exact rational change-of-basis matrices identify the singular values of the centered Laplacians; the largest two are 11/3 and 7/3 in both cases. Both second Ky Fan norms therefore equal 6, contradicting the equality characterization. This also contradicts the uniqueness assertion of the source's Theorem 5.9 at order six. The third norm, the global upper bound and an equality classification for general orders are not asserted here.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/LinMiaoYuShengSecondNormUniquenessRefutation.Gmn`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/LinMiaoYuShengSecondNormUniquenessRefutation.LI`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/LinMiaoYuShengSecondNormUniquenessRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/LinMiaoYuShengSecondNormUniquenessRefutation.result`
- Dependency: [D5/S3/Combinatorics/Graph/KyFanGap/Defs](Defs.md)
