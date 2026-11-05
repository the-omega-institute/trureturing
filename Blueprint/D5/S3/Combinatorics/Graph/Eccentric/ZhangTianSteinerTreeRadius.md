# Steiner diameter and anchored radius of trees

## Abstract

Terminal-cut averaging proves Zhang–Tian Conjecture 5.1 for every finite tree.

**Definition 1.1 (Steiner distance).**

$$\forall (V : Type), \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (S : \operatorname{Finset}\left(V\right)), \operatorname{steinerDist}\left(G, S\right) = \operatorname{sInf}\left(\{ m : \mathbb{N} \mid \exists (H : G.Subgraph), (H.Connected) \land (((S : \operatorname{Set}\left(V\right)) \subseteq H.verts) \land (H.edgeSet.ncard = m)) \}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.steinerDist` (`✓ std3`).

*Citation.* Qingnan Zhang; Yingzhi Tian (2025). *On the Steiner k-diameter and Steiner (k, k′)-radius of trees*. DOI: [10.48550/arXiv.2511.22492](https://doi.org/10.48550/arXiv.2511.22492). URL: <https://arxiv.org/abs/2511.22492v1>.

*Commentary.*

Page 2: "The Steiner distance d_G(S) among the vertices of S (or simply the distance of S) is defined as the minimum size among all connected subgraphs whose vertex sets contain S." The size of a graph is its number of edges. The natural infimum ranges over actual connected subgraphs, recording both vertices and edges. The displayed set coercion views the finite terminal set as a set of vertices.

**Definition 1.2 (Steiner vertex eccentricity).**

$$\forall (V : Type), \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (k : \mathbb{N}), \forall (v : V), \operatorname{steinerEcc}\left(G, k, v\right) = \operatorname{sSup}\left(\{ m : \mathbb{N} \mid \exists (S : \operatorname{Finset}\left(V\right)), (v \in S) \land ((S.card = k) \land (\operatorname{steinerDist}\left(G, S\right) = m)) \}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.steinerEcc` (`✓ std3`).

*Citation.* Qingnan Zhang; Yingzhi Tian (2025). *On the Steiner k-diameter and Steiner (k, k′)-radius of trees*. DOI: [10.48550/arXiv.2511.22492](https://doi.org/10.48550/arXiv.2511.22492). URL: <https://arxiv.org/abs/2511.22492v1>.

*Commentary.*

Page 2: "The Steiner k-eccentricity ε_k(v; G) of a vertex v in G is defined by max{d_G(S) : v ∈ S ⊆ V(G), |S| = k}, where k ≥ 2." Finite subsets of the vertex type express S ⊆ V(G); their cardinality is the number of terminals.

**Definition 1.3 (Steiner diameter).**

$$\forall (V : Type), \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (k : \mathbb{N}), \operatorname{steinerDiam}\left(G, k\right) = \operatorname{sSup}\left(\{ m : \mathbb{N} \mid \exists (v : V), \operatorname{steinerEcc}\left(G, k, v\right) = m \}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.steinerDiam` (`✓ std3`).

*Citation.* Qingnan Zhang; Yingzhi Tian (2025). *On the Steiner k-diameter and Steiner (k, k′)-radius of trees*. DOI: [10.48550/arXiv.2511.22492](https://doi.org/10.48550/arXiv.2511.22492). URL: <https://arxiv.org/abs/2511.22492v1>.

*Commentary.*

Page 2: "The Steiner k-radius of G is Sr_k(G) = min{ε_k(v) : v ∈ V(G)}, and the Steiner k-diameter of G is Sd_k(G) = max{ε_k(v) : v ∈ V(G)}." steinerDiam is the natural supremum of the vertex eccentricities; the radius mentioned in this source sentence is not a separate definition here.

**Definition 1.4 (Anchored Steiner eccentricity).**

$$\forall (V : Type), \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (k : \mathbb{N}), \forall (B : \operatorname{Finset}\left(V\right)), \operatorname{steinerSetEcc}\left(G, k, B\right) = \operatorname{sSup}\left(\{ m : \mathbb{N} \mid \exists (S : \operatorname{Finset}\left(V\right)), (B \subseteq S) \land ((S.card = k) \land (\operatorname{steinerDist}\left(G, S\right) = m)) \}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.steinerSetEcc` (`✓ std3`).

*Citation.* Qingnan Zhang; Yingzhi Tian (2025). *On the Steiner k-diameter and Steiner (k, k′)-radius of trees*. DOI: [10.48550/arXiv.2511.22492](https://doi.org/10.48550/arXiv.2511.22492). URL: <https://arxiv.org/abs/2511.22492v1>.

*Commentary.*

Page 2: "The Steiner (k, k′)-eccentricity ε_{k,k′}(S′; G) of a k′-subset S′ in G is defined as the maximum Steiner distance over k-subsets of V(G) that include S′, that is, ε_{k,k′}(S′; G) = max{d_G(S) : S′ ⊆ S ⊆ V(G), |S| = k}, where k ≥ 2 and k ≥ k′ ≥ 1." The anchor cardinality is supplied by the theorem hypotheses, while steinerSetEcc takes the anchor set itself.

**Definition 1.5 (Anchored Steiner radius).**

$$\forall (V : Type), \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (k : \mathbb{N}), \forall (r : \mathbb{N}), \operatorname{steinerRadius}\left(G, k, r\right) = \operatorname{sInf}\left(\{ m : \mathbb{N} \mid \exists (B : \operatorname{Finset}\left(V\right)), (B.card = r) \land (\operatorname{steinerSetEcc}\left(G, k, B\right) = m) \}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.steinerRadius` (`✓ std3`).

*Citation.* Qingnan Zhang; Yingzhi Tian (2025). *On the Steiner k-diameter and Steiner (k, k′)-radius of trees*. DOI: [10.48550/arXiv.2511.22492](https://doi.org/10.48550/arXiv.2511.22492). URL: <https://arxiv.org/abs/2511.22492v1>.

*Commentary.*

Page 2: "The Steiner (k, k′)-radius of G is Sr_{k,k′}(G) = min{ε_{k,k′}(S′; G) : S′ ⊆ V(G), |S′| = k′}, where k′ ≥ 1." steinerRadius takes the natural infimum over every anchor set of the specified cardinality.

**Definition 1.6 (Zhang–Tian Conjecture 5.1).**

$$(claim) \Leftrightarrow (\forall (V : Type), [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], \forall (T : \operatorname{SimpleGraph}\left(V\right)), \forall (k : \mathbb{N}), \forall (r : \mathbb{N}), (T.IsTree) \Rightarrow ((k \le \operatorname{Fintype.card}\left(V\right)) \Rightarrow ((3 \le k) \Rightarrow ((r < k) \Rightarrow ((1 \le r) \Rightarrow ((\operatorname{steinerDiam}\left(T, k\right) : \mathbb{Q}) \le \frac{(k : \mathbb{Q})}{(k : \mathbb{Q}) - (r : \mathbb{Q})} \cdot (\operatorname{steinerRadius}\left(T, k, r\right) : \mathbb{Q}) - \frac{(r : \mathbb{Q}) \cdot ((r : \mathbb{Q}) - 1)}{(k : \mathbb{Q}) - (r : \mathbb{Q})}))))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.claim` (`✓ std3`).

*Citation.* Qingnan Zhang; Yingzhi Tian (2025). *On the Steiner k-diameter and Steiner (k, k′)-radius of trees*. DOI: [10.48550/arXiv.2511.22492](https://doi.org/10.48550/arXiv.2511.22492). URL: <https://arxiv.org/abs/2511.22492v1>.

*Commentary.*

Conjecture 5.1, page 14: "Let n, k, k′ be integers with n ≥ k ≥ 3 and k > k′ ≥ 1 and let T be a tree with order n. Then Sd_k(T) ≤ k/(k − k′) Sr_{k,k′}(T) − k′(k′ − 1)/(k − k′)." Here n is Fintype.card V and r denotes k′. Natural-valued distances, k and r are cast into ℚ before the displayed divisions and subtractions. Finiteness and decidable equality appear as anonymous instance arguments; IsTree means connected and acyclic.

**Definition 1.7 (Terminal separation after edge deletion).**

$$\forall (V : Type), \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (S : \operatorname{Finset}\left(V\right)), \forall (e : \operatorname{Sym2}\left(V\right)), (\operatorname{Separates}\left(G, S, e\right)) \Leftrightarrow (\exists (a : V), (a \in S) \land (\exists (b : V), (b \in S) \land (\neg ((G.deleteEdges\left(\{e\}\right)).Reachable\left(a, b\right)))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.Separates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Qingnan Zhang; Yingzhi Tian (2025). *On the Steiner k-diameter and Steiner (k, k′)-radius of trees*. DOI: [10.48550/arXiv.2511.22492](https://doi.org/10.48550/arXiv.2511.22492). URL: <https://arxiv.org/abs/2511.22492v1>.

*Commentary.*

Separates T S e means that deleting e disconnects two terminals of S. No choice of an orientation or a component is part of this predicate.

**Definition 1.8 (Separating edges).**

$$\forall (V : Type), [\operatorname{Fintype}\left(V\right)], \forall (T : \operatorname{SimpleGraph}\left(V\right)), \forall (S : \operatorname{Finset}\left(V\right)), \operatorname{cutEdges}\left(T, S\right) = \operatorname{Finset.filter}\left(\operatorname{Separates}\left(T, S\right), T.edgeFinset\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.cutEdges` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Qingnan Zhang; Yingzhi Tian (2025). *On the Steiner k-diameter and Steiner (k, k′)-radius of trees*. DOI: [10.48550/arXiv.2511.22492](https://doi.org/10.48550/arXiv.2511.22492). URL: <https://arxiv.org/abs/2511.22492v1>.

*Commentary.*

cutEdges filters the graph's finite edge set by terminal separation. Each undirected edge is counted once as an element of Sym2 V.

**Theorem 1.9 (Distance counts separating edges).**

$$\forall (V : Type), [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], \forall (T : \operatorname{SimpleGraph}\left(V\right)), (T.IsTree) \Rightarrow (\forall (S : \operatorname{Finset}\left(V\right)), (S.Nonempty) \Rightarrow (\operatorname{steinerDist}\left(T, S\right) = (\operatorname{cutEdges}\left(T, S\right)).card))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.steinerDist_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Qingnan Zhang; Yingzhi Tian (2025). *On the Steiner k-diameter and Steiner (k, k′)-radius of trees*. DOI: [10.48550/arXiv.2511.22492](https://doi.org/10.48550/arXiv.2511.22492). URL: <https://arxiv.org/abs/2511.22492v1>.

*Commentary.*

For a finite tree and a nonempty terminal set, the defining minimum equals the number of separating edges. The intersection of all connected terminal-containing subgraphs is connected because the tree has a unique path between any two vertices. An edge in that intersection separates terminals: otherwise the deletion component containing a chosen terminal contains all terminals and excludes the edge.

**Theorem 1.10 (A bound for every pair of terminal sets).**

$$\forall (V : Type), [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], \forall (T : \operatorname{SimpleGraph}\left(V\right)), (T.IsTree) \Rightarrow (\forall (A : \operatorname{Finset}\left(V\right)), \forall (B : \operatorname{Finset}\left(V\right)), \forall (k : \mathbb{N}), \forall (r : \mathbb{N}), (A.card = k) \Rightarrow ((B.card = r) \Rightarrow ((r < k) \Rightarrow ((1 \le r) \Rightarrow ((k \le \operatorname{Fintype.card}\left(V\right)) \Rightarrow ((k - r) \cdot \operatorname{steinerDist}\left(T, A\right) + r \cdot \operatorname{steinerDist}\left(T, B\right) \le k \cdot \operatorname{steinerSetEcc}\left(T, k, B\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.pointwise_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Qingnan Zhang; Yingzhi Tian (2025). *On the Steiner k-diameter and Steiner (k, k′)-radius of trees*. DOI: [10.48550/arXiv.2511.22492](https://doi.org/10.48550/arXiv.2511.22492). URL: <https://arxiv.org/abs/2511.22492v1>.

*Commentary.*

For every k-set A and r-set B in a finite tree, with 1 ≤ r < k and enough vertices, (k−r) steinerDist T A + r steinerDist T B ≤ k steinerSetEcc T k B. Every edge of the B-hull persists when B is enlarged. For each edge of the A-hull outside it, select an A-terminal separated from a B-terminal. That edge persists whenever the selected terminal belongs to a sampled (k−r)-subset of A. Double counting these samples yields the inequality. The sets may overlap, and A need not maximize the distance.

**Theorem 1.11 (The conjecture holds for all finite trees).**

$$\forall (V : Type), [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], \forall (T : \operatorname{SimpleGraph}\left(V\right)), \forall (k : \mathbb{N}), \forall (r : \mathbb{N}), (T.IsTree) \Rightarrow ((k \le \operatorname{Fintype.card}\left(V\right)) \Rightarrow ((3 \le k) \Rightarrow ((r < k) \Rightarrow ((1 \le r) \Rightarrow ((\operatorname{steinerDiam}\left(T, k\right) : \mathbb{Q}) \le \frac{(k : \mathbb{Q})}{(k : \mathbb{Q}) - (r : \mathbb{Q})} \cdot (\operatorname{steinerRadius}\left(T, k, r\right) : \mathbb{Q}) - \frac{(r : \mathbb{Q}) \cdot ((r : \mathbb{Q}) - 1)}{(k : \mathbb{Q}) - (r : \mathbb{Q})})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhang-tian-2025-steiner-diameter-radius-trees` (proved) by `D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhang-tian-2025-steiner-diameter-radius-trees","declaration_gid":"D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Qingnan Zhang; Yingzhi Tian (2025). *On the Steiner k-diameter and Steiner (k, k′)-radius of trees*. DOI: [10.48550/arXiv.2511.22492](https://doi.org/10.48550/arXiv.2511.22492). URL: <https://arxiv.org/abs/2511.22492v1>.

*Commentary.*

Choose terminal sets attaining the Steiner diameter and the anchored radius. The pointwise inequality retains the entire anchor hull, whose edge count is at least r−1. This supplies the additive r(r−1) correction. Division by the positive rational k−r gives the displayed inequality.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.Separates`
- Truth anchor: `D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.cutEdges`
- Truth anchor: `D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.pointwise_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.steinerDiam`
- Truth anchor: `D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.steinerDist`
- Truth anchor: `D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.steinerDist_cut`
- Truth anchor: `D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.steinerEcc`
- Truth anchor: `D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.steinerRadius`
- Truth anchor: `D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.steinerSetEcc`
