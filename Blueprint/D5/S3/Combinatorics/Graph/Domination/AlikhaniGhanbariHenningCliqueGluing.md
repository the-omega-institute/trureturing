# Strong domination under clique gluing

## Abstract

The strong domination number of a clique gluing satisfies Inequality (4) of Alikhani, Ghanbari and Henning for every clique size at least two.

**Definition 1.1 (Strong dominating sets).**

$$\forall (V : Type), [\operatorname{Fintype}\left(V\right)] \forall (G : \operatorname{SimpleGraph}\left(V\right)), [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] \forall (D : \operatorname{Finset}\left(V\right)), \operatorname{IsStrongDominatingSet}\left(G, D\right) \Leftrightarrow (\forall (x : V), (\neg x \in D) \Rightarrow (\exists (y : V), (y \in D) \land ((\operatorname{SimpleGraph}.\operatorname{Adj}\left(G, x, y\right)) \land (\operatorname{SimpleGraph}.\operatorname{degree}\left(G, x\right) \le \operatorname{SimpleGraph}.\operatorname{degree}\left(G, y\right)))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/AlikhaniGhanbariHenningCliqueGluing.IsStrongDominatingSet` (`✓ std3`).

*Citation.* Saeid Alikhani, Nima Ghanbari, Michael A. Henning (2026). *Strong domination number of graphs from primary subgraphs*. DOI: [10.2989/16073606.2025.2574046](https://doi.org/10.2989/16073606.2025.2574046). URL: <https://www.tandfonline.com/doi/full/10.2989/16073606.2025.2574046>.

*Commentary.*

Abstract, p. 195: "A set D of vertices is a strong dominating set in a graph G, if for every vertex x ∈ V(G) \ D there is a vertex y ∈ D with xy ∈ E(G) and deg(x) ≤ deg(y). The strong domination number γst(G) of G is the minimum cardinality of a strong dominating set in G." Finite sets encode vertex subsets. SimpleGraph.degree counts each distinct neighbour once.

**Definition 1.2 (The minimum cardinality).**

$$\forall (V : Type), [\operatorname{Fintype}\left(V\right)] \forall (G : \operatorname{SimpleGraph}\left(V\right)), [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] \operatorname{strongDominationNumber}\left(G\right) = \operatorname{sInf}\left(\{ k : \mathbb{N} \mid \exists (D : \operatorname{Finset}\left(V\right)), (\operatorname{IsStrongDominatingSet}\left(G, D\right)) \land (\operatorname{Finset}.\operatorname{card}\left(D\right) = k) \}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/AlikhaniGhanbariHenningCliqueGluing.strongDominationNumber` (`✓ std3`).

*Citation.* Saeid Alikhani, Nima Ghanbari, Michael A. Henning (2026). *Strong domination number of graphs from primary subgraphs*. DOI: [10.2989/16073606.2025.2574046](https://doi.org/10.2989/16073606.2025.2574046). URL: <https://www.tandfonline.com/doi/full/10.2989/16073606.2025.2574046>.

*Commentary.*

Abstract, p. 195: "A set D of vertices is a strong dominating set in a graph G, if for every vertex x ∈ V(G) \ D there is a vertex y ∈ D with xy ∈ E(G) and deg(x) ≤ deg(y). The strong domination number γst(G) of G is the minimum cardinality of a strong dominating set in G." The full vertex set is strong dominating, so the natural-number infimum of attained sizes is attained.

**Definition 1.3 (The second graph's vertex map).**

$$\forall (r : \mathbb{N}), \forall (V1 : Type), \forall (V2 : Type), [\operatorname{DecidableEq}\left(V2\right)] \forall (A : \operatorname{Function}.\operatorname{Embedding}\left(\operatorname{Fin}\left(r\right), V1\right)), \forall (B : \operatorname{Function}.\operatorname{Embedding}\left(\operatorname{Fin}\left(r\right), V2\right)), \forall (w : V2), \operatorname{embedRight}\left(A, B, w\right) = (\operatorname{if} h : w \in \operatorname{Set}.\operatorname{range}\left(B\right) \operatorname{then} \operatorname{Sum}.\operatorname{inl}\left(A\left(\operatorname{Function}.\operatorname{Embedding}.\operatorname{invOfMemRange}\left(B, \langle w, h\rangle\right)\right)\right) \operatorname{else} \operatorname{Sum}.\operatorname{inr}\left(\langle w, h\rangle\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/AlikhaniGhanbariHenningCliqueGluing.embedRight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Saeid Alikhani, Nima Ghanbari, Michael A. Henning (2026). *Strong domination number of graphs from primary subgraphs*. DOI: [10.2989/16073606.2025.2574046](https://doi.org/10.2989/16073606.2025.2574046). URL: <https://www.tandfonline.com/doi/full/10.2989/16073606.2025.2574046>.

*Commentary.*

A vertex B i maps to Sum.inl (A i). A vertex outside the range of B maps to the right summand, with its proof of exclusion. Function.Embedding.invOfMemRange recovers the unique index in the range of B.

**Definition 1.4 (The glued graph).**

$$\forall (r : \mathbb{N}), \forall (V1 : Type), \forall (V2 : Type), [\operatorname{DecidableEq}\left(V2\right)] \forall (G1 : \operatorname{SimpleGraph}\left(V1\right)), \forall (G2 : \operatorname{SimpleGraph}\left(V2\right)), \forall (A : \operatorname{Function}.\operatorname{Embedding}\left(\operatorname{Fin}\left(r\right), V1\right)), \forall (B : \operatorname{Function}.\operatorname{Embedding}\left(\operatorname{Fin}\left(r\right), V2\right)), \operatorname{glue}\left(G1, G2, A, B\right) = \operatorname{SimpleGraph}.\operatorname{fromRel}\left((\operatorname{fun} (p : \operatorname{Sum}\left(V1, \{ w : V2 \mid \neg w \in \operatorname{Set}.\operatorname{range}\left(B\right) \}\right)) \mapsto (\operatorname{fun} (q : \operatorname{Sum}\left(V1, \{ w : V2 \mid \neg w \in \operatorname{Set}.\operatorname{range}\left(B\right) \}\right)) \mapsto (\exists (x : V1), \exists (y : V1), (p = \operatorname{Sum}.\operatorname{inl}\left(x\right)) \land ((q = \operatorname{Sum}.\operatorname{inl}\left(y\right)) \land (\operatorname{SimpleGraph}.\operatorname{Adj}\left(G1, x, y\right)))) \lor (\exists (x : V2), \exists (y : V2), (p = \operatorname{embedRight}\left(A, B, x\right)) \land ((q = \operatorname{embedRight}\left(A, B, y\right)) \land (\operatorname{SimpleGraph}.\operatorname{Adj}\left(G2, x, y\right))))))\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/AlikhaniGhanbariHenningCliqueGluing.glue` (`✓ std3`).

*Citation.* Saeid Alikhani, Nima Ghanbari, Michael A. Henning (2026). *Strong domination number of graphs from primary subgraphs*. DOI: [10.2989/16073606.2025.2574046](https://doi.org/10.2989/16073606.2025.2574046). URL: <https://www.tandfonline.com/doi/full/10.2989/16073606.2025.2574046>.

*Commentary.*

Section 1, p. 196: "Choose a clique of cardinality r from each Gi, i = 1, 2, and form a new graph G from the union of G1 and G2 by identifying the two chosen r-cliques in an arbitrary manner." The vertex type retains every vertex of G1 and exactly the vertices of G2 outside B. SimpleGraph.fromRel combines the two edge relations; repeated edges of the common clique occur once.

**Definition 1.5 (External neighbours of a clique vertex).**

$$\forall (r : \mathbb{N}), \forall (V1 : Type), [\operatorname{Fintype}\left(V1\right)] [\operatorname{DecidableEq}\left(V1\right)] \forall (G1 : \operatorname{SimpleGraph}\left(V1\right)), [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G1\right)\right)] \forall (A : \operatorname{Function}.\operatorname{Embedding}\left(\operatorname{Fin}\left(r\right), V1\right)), \forall (i : \operatorname{Fin}\left(r\right)), \operatorname{X}\left(G1, A, i\right) = \operatorname{SimpleGraph}.\operatorname{neighborFinset}\left(G1, A\left(i\right)\right) \setminus \operatorname{Finset}.\operatorname{map}\left(A, \operatorname{Finset}.\operatorname{univ}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/AlikhaniGhanbariHenningCliqueGluing.X` (`✓ std3`).

*Citation.* Saeid Alikhani, Nima Ghanbari, Michael A. Henning (2026). *Strong domination number of graphs from primary subgraphs*. DOI: [10.2989/16073606.2025.2574046](https://doi.org/10.2989/16073606.2025.2574046). URL: <https://www.tandfonline.com/doi/full/10.2989/16073606.2025.2574046>.

*Commentary.*

Problem 1, p. 202: "For r ≥ 2, let G1 and G2 be connected graphs both of order at least r + 1 that contain r-cliques A = {u1, u2, …, ur} and B = {v1, v2, …, vr}, respectively. Let Xi = NG1(ui) \ A and Yi = NG2(vi) \ B for i ∈ [r], and let ΣX,Y = Σ_{i=1}^r |Xi| + Σ_{i=1}^r |Yi|. Let G ∈ G1 ∪Kr G2 be obtained by a Kr-gluing of the graphs G1 and G2 by identifying the cliques A and B, where we identify the vertices ui and vi for i ∈ [r]. Determine a best possible lower bound on γst(G) in terms of γst(G1), γst(G2) and ΣX,Y. In particular, is it true that γst(G) ≥ γst(G1) + γst(G2) − 1 − ΣX,Y? (4)" X G1 A i is Xi, and X G2 B i is Yi. Finset.univ.map A is the enumerated clique. Index i in Fin r corresponds to index i+1 in the paper.

**Definition 1.6 (The total external-neighbour count).**

$$\forall (r : \mathbb{N}), \forall (V1 : Type), \forall (V2 : Type), [\operatorname{Fintype}\left(V1\right)] [\operatorname{DecidableEq}\left(V1\right)] [\operatorname{Fintype}\left(V2\right)] [\operatorname{DecidableEq}\left(V2\right)] \forall (G1 : \operatorname{SimpleGraph}\left(V1\right)), [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G1\right)\right)] \forall (G2 : \operatorname{SimpleGraph}\left(V2\right)), [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G2\right)\right)] \forall (A : \operatorname{Function}.\operatorname{Embedding}\left(\operatorname{Fin}\left(r\right), V1\right)), \forall (B : \operatorname{Function}.\operatorname{Embedding}\left(\operatorname{Fin}\left(r\right), V2\right)), \operatorname{sigmaXY}\left(G1, G2, A, B\right) = (\sum_{i : \operatorname{Fin}\left(r\right)} \operatorname{Finset}.\operatorname{card}\left(\operatorname{X}\left(G1, A, i\right)\right)) + (\sum_{i : \operatorname{Fin}\left(r\right)} \operatorname{Finset}.\operatorname{card}\left(\operatorname{X}\left(G2, B, i\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/AlikhaniGhanbariHenningCliqueGluing.sigmaXY` (`✓ std3`).

*Citation.* Saeid Alikhani, Nima Ghanbari, Michael A. Henning (2026). *Strong domination number of graphs from primary subgraphs*. DOI: [10.2989/16073606.2025.2574046](https://doi.org/10.2989/16073606.2025.2574046). URL: <https://www.tandfonline.com/doi/full/10.2989/16073606.2025.2574046>.

*Commentary.*

Problem 1, p. 202: "For r ≥ 2, let G1 and G2 be connected graphs both of order at least r + 1 that contain r-cliques A = {u1, u2, …, ur} and B = {v1, v2, …, vr}, respectively. Let Xi = NG1(ui) \ A and Yi = NG2(vi) \ B for i ∈ [r], and let ΣX,Y = Σ_{i=1}^r |Xi| + Σ_{i=1}^r |Yi|. Let G ∈ G1 ∪Kr G2 be obtained by a Kr-gluing of the graphs G1 and G2 by identifying the cliques A and B, where we identify the vertices ui and vi for i ∈ [r]. Determine a best possible lower bound on γst(G) in terms of γst(G1), γst(G2) and ΣX,Y. In particular, is it true that γst(G) ≥ γst(G1) + γst(G2) − 1 − ΣX,Y? (4)" Each cardinality is counted separately for each clique vertex; a vertex adjacent to several clique vertices contributes several times.

**Definition 1.7 (Inequality (4) on the whole stated domain).**

$$claim \Leftrightarrow (\forall (r : \mathbb{N}), (2 \le r) \Rightarrow (\forall (V1 : Type), \forall (V2 : Type), [\operatorname{Fintype}\left(V1\right)] [\operatorname{DecidableEq}\left(V1\right)] [\operatorname{Fintype}\left(V2\right)] [\operatorname{DecidableEq}\left(V2\right)] \forall (G1 : \operatorname{SimpleGraph}\left(V1\right)), \forall (G2 : \operatorname{SimpleGraph}\left(V2\right)), \forall (A : \operatorname{Function}.\operatorname{Embedding}\left(\operatorname{Fin}\left(r\right), V1\right)), \forall (B : \operatorname{Function}.\operatorname{Embedding}\left(\operatorname{Fin}\left(r\right), V2\right)), (\operatorname{SimpleGraph}.\operatorname{Connected}\left(G1\right)) \Rightarrow ((\operatorname{SimpleGraph}.\operatorname{Connected}\left(G2\right)) \Rightarrow ((r + 1 \le \operatorname{Fintype}.\operatorname{card}\left(V1\right)) \Rightarrow ((r + 1 \le \operatorname{Fintype}.\operatorname{card}\left(V2\right)) \Rightarrow ((\operatorname{SimpleGraph}.\operatorname{IsClique}\left(G1, \operatorname{Set}.\operatorname{range}\left(A\right)\right)) \Rightarrow ((\operatorname{SimpleGraph}.\operatorname{IsClique}\left(G2, \operatorname{Set}.\operatorname{range}\left(B\right)\right)) \Rightarrow ((\operatorname{strongDominationNumber}\left(G1\right) : \mathbb{Z}) + (\operatorname{strongDominationNumber}\left(G2\right) : \mathbb{Z}) - 1 - (\operatorname{sigmaXY}\left(G1, G2, A, B\right) : \mathbb{Z}) \le (\operatorname{strongDominationNumber}\left(\operatorname{glue}\left(G1, G2, A, B\right)\right) : \mathbb{Z})))))))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/AlikhaniGhanbariHenningCliqueGluing.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Saeid Alikhani, Nima Ghanbari, Michael A. Henning (2026). *Strong domination number of graphs from primary subgraphs*. DOI: [10.2989/16073606.2025.2574046](https://doi.org/10.2989/16073606.2025.2574046). URL: <https://www.tandfonline.com/doi/full/10.2989/16073606.2025.2574046>.

*Commentary.*

Problem 1, p. 202: "For r ≥ 2, let G1 and G2 be connected graphs both of order at least r + 1 that contain r-cliques A = {u1, u2, …, ur} and B = {v1, v2, …, vr}, respectively. Let Xi = NG1(ui) \ A and Yi = NG2(vi) \ B for i ∈ [r], and let ΣX,Y = Σ_{i=1}^r |Xi| + Σ_{i=1}^r |Yi|. Let G ∈ G1 ∪Kr G2 be obtained by a Kr-gluing of the graphs G1 and G2 by identifying the cliques A and B, where we identify the vertices ui and vi for i ∈ [r]. Determine a best possible lower bound on γst(G) in terms of γst(G1), γst(G2) and ΣX,Y. In particular, is it true that γst(G) ≥ γst(G1) + γst(G2) − 1 − ΣX,Y? (4)" The displayed proposition answers the final question affirmatively. The two graph orders are Fintype.card, the cliques are the ranges of embeddings from Fin r, and all subtraction is in the integers. Adjacency of the glued graph is decided classically.

**Theorem 1.8 (The lower bound for every r at least two).**

$$\forall (r : \mathbb{N}), (2 \le r) \Rightarrow (\forall (V1 : Type), \forall (V2 : Type), [\operatorname{Fintype}\left(V1\right)] [\operatorname{DecidableEq}\left(V1\right)] [\operatorname{Fintype}\left(V2\right)] [\operatorname{DecidableEq}\left(V2\right)] \forall (G1 : \operatorname{SimpleGraph}\left(V1\right)), \forall (G2 : \operatorname{SimpleGraph}\left(V2\right)), \forall (A : \operatorname{Function}.\operatorname{Embedding}\left(\operatorname{Fin}\left(r\right), V1\right)), \forall (B : \operatorname{Function}.\operatorname{Embedding}\left(\operatorname{Fin}\left(r\right), V2\right)), (\operatorname{SimpleGraph}.\operatorname{Connected}\left(G1\right)) \Rightarrow ((\operatorname{SimpleGraph}.\operatorname{Connected}\left(G2\right)) \Rightarrow ((r + 1 \le \operatorname{Fintype}.\operatorname{card}\left(V1\right)) \Rightarrow ((r + 1 \le \operatorname{Fintype}.\operatorname{card}\left(V2\right)) \Rightarrow ((\operatorname{SimpleGraph}.\operatorname{IsClique}\left(G1, \operatorname{Set}.\operatorname{range}\left(A\right)\right)) \Rightarrow ((\operatorname{SimpleGraph}.\operatorname{IsClique}\left(G2, \operatorname{Set}.\operatorname{range}\left(B\right)\right)) \Rightarrow ((\operatorname{strongDominationNumber}\left(G1\right) : \mathbb{Z}) + (\operatorname{strongDominationNumber}\left(G2\right) : \mathbb{Z}) - 1 - (\operatorname{sigmaXY}\left(G1, G2, A, B\right) : \mathbb{Z}) \le (\operatorname{strongDominationNumber}\left(\operatorname{glue}\left(G1, G2, A, B\right)\right) : \mathbb{Z}))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/AlikhaniGhanbariHenningCliqueGluing.result` (`✓ std3`). ∎

*Resolves.* `Problems/alikhani-ghanbari-henning-clique-gluing-problem-1` (proved) by `D5/S3/Combinatorics/Graph/Domination/AlikhaniGhanbariHenningCliqueGluing.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"alikhani-ghanbari-henning-clique-gluing-problem-1","declaration_gid":"D5/S3/Combinatorics/Graph/Domination/AlikhaniGhanbariHenningCliqueGluing.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Saeid Alikhani, Nima Ghanbari, Michael A. Henning (2026). *Strong domination number of graphs from primary subgraphs*. DOI: [10.2989/16073606.2025.2574046](https://doi.org/10.2989/16073606.2025.2574046). URL: <https://www.tandfonline.com/doi/full/10.2989/16073606.2025.2574046>.

*Commentary.*

Restrict a minimum strong dominating set to each graph outside the common clique. In each factor, add a clique vertex of maximum degree; it strongly dominates the rest of the clique. If the original set meets the clique, also add the external neighbours of that clique. Every remaining exterior vertex keeps its original dominator and degree comparison. The two restrictions then have total size at most the original size plus one plus sigmaXY: a selected clique vertex pays for one of the two added clique vertices. If the original set misses the clique, connectedness and the proper clique range give at least one external neighbour, which pays for the extra vertex. Taking minimum sizes and rearranging in the integers yields the displayed bound. General sharpness of the source family and bounds using finer parameters are not asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/AlikhaniGhanbariHenningCliqueGluing.IsStrongDominatingSet`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/AlikhaniGhanbariHenningCliqueGluing.X`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/AlikhaniGhanbariHenningCliqueGluing.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/AlikhaniGhanbariHenningCliqueGluing.embedRight`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/AlikhaniGhanbariHenningCliqueGluing.glue`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/AlikhaniGhanbariHenningCliqueGluing.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/AlikhaniGhanbariHenningCliqueGluing.sigmaXY`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/AlikhaniGhanbariHenningCliqueGluing.strongDominationNumber`
