# Three central distances do not give the proposed edge minimum

## Abstract

A four-point ultrametric has more central edges than a three-central metric.

**Definition 1.1 (The center of distances).**

$$\forall X \in Type,\; [\operatorname{MetricSpace}\left(X\right)] \operatorname{center}\left(X\right) = \{t:\mathbb{R} \mid (0 \le t) \land (\forall p \in X,\; \exists y \in X,\; \operatorname{dist}\left(y, p\right) = t)\}$$

*Formalization.* `D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges.center` (`✓ std3`).

*Citation.* Oleksiy Dovgoshey and Olga Rovenska (2026). *On the Graph Corresponding to Center of Distances of Metric Space*. DOI: [10.48550/arXiv.2610.11596](https://doi.org/10.48550/arXiv.2610.11596). URL: <https://arxiv.org/abs/2610.11596v1>.

*Commentary.*

Definition 1.1 (p. 1): “Let (Y,ρ) be a metric space. The center of distances of (Y,ρ) is the subset C(Y)⊆ℝ⁺, such that t∈ C(Y) if and only if the equation ρ(y,p)=t has a solution for every p∈ Y.” The source uses the nonnegative reals, including zero. The real variable t is realized as a distance from every p; the realizing point y may depend on p.

**Definition 1.2 (The central graph).**

$$\forall X \in Type,\; [\operatorname{MetricSpace}\left(X\right)] \operatorname{centralGraph}\left(X\right) = \operatorname{SimpleGraph}.\operatorname{fromRel}\left((\lambda u:X \mapsto (\lambda v:X \mapsto \operatorname{dist}\left(u, v\right) \in \operatorname{center}\left(X\right)))\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges.centralGraph` (`✓ std3`).

*Citation.* Oleksiy Dovgoshey and Olga Rovenska (2026). *On the Graph Corresponding to Center of Distances of Metric Space*. DOI: [10.48550/arXiv.2610.11596](https://doi.org/10.48550/arXiv.2610.11596). URL: <https://arxiv.org/abs/2610.11596v1>.

*Commentary.*

Definition 1.2 (p. 1): “Let (Y,ρ) be a metric space and let C(Y) be the center of distances of (Y,ρ). The central graph CG_Y of (Y,ρ) is a simple graph such that V(CG_Y)=Y and {u,v}∈ E(CG_Y) ⇔ ρ(u,v)∈ C(Y) for all u,v∈ Y. We will write that the central graph CG_Y is k-central if k=|C(Y)|.” SimpleGraph.fromRel removes loops and symmetrizes the relation. Symmetry of distance gives precisely the displayed adjacency for distinct vertices. Edge sets contain unordered pairs, counted once.

**Definition 1.3 (The diametrical graph).**

$$\forall X \in Type,\; [\operatorname{MetricSpace}\left(X\right)] \operatorname{diametricalGraph}\left(X\right) = \operatorname{SimpleGraph}.\operatorname{fromRel}\left((\lambda u:X \mapsto (\lambda v:X \mapsto \operatorname{dist}\left(u, v\right) = \operatorname{Metric}.\operatorname{diam}\left((\operatorname{Set}.\operatorname{univ}:\operatorname{Set}\left(X\right))\right)))\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges.diametricalGraph` (`✓ std3`).

*Citation.* Oleksiy Dovgoshey and Olga Rovenska (2026). *On the Graph Corresponding to Center of Distances of Metric Space*. DOI: [10.48550/arXiv.2610.11596](https://doi.org/10.48550/arXiv.2610.11596). URL: <https://arxiv.org/abs/2610.11596v1>.

*Commentary.*

Definition 2.14 (p. 4): “Let (Y,ρ) be a finite metric space with |Y|≥ 2. The diametrical graph G_Y of (Y,ρ) is a graph such that V(G)=Y and, for all u,v∈ Y, {u,v}∈ E(G_{Y}) ⇔ ρ(u,v)=diamY.” The diameter is Metric.diam of the whole carrier; only finite carriers with at least four points occur in the conjecture.

**Definition 1.4 (The bipartite graph with two stars).**

$$\forall X \in Type,\; [\operatorname{MetricSpace}\left(X\right)] \operatorname{conditionI}\left(X\right) \Leftrightarrow \left(\exists A \in \operatorname{Set}\left(X\right),\; \exists B \in \operatorname{Set}\left(X\right),\; \exists a \in A,\; \exists b \in B,\; (\operatorname{Disjoint}\left(A, B\right)) \land ((\operatorname{Set}.\operatorname{union}\left(A, B\right) = \operatorname{Set}.\operatorname{univ}) \land ((\operatorname{min}\left(\operatorname{Nat}.\operatorname{card}\left(A\right), \operatorname{Nat}.\operatorname{card}\left(B\right)\right) = 2) \land ((\operatorname{diametricalGraph}\left(X\right) = \operatorname{SimpleGraph}.\operatorname{map}\left(\operatorname{Sum}.\operatorname{elim}\left((\lambda z:A \mapsto (z:X)), (\lambda z:B \mapsto (z:X))\right), \operatorname{completeBipartiteGraph}\left(A, B\right)\right)) \land (\operatorname{centralGraph}\left(X\right) = \operatorname{Max}.\operatorname{max}\left(\operatorname{Max}.\operatorname{max}\left(\operatorname{diametricalGraph}\left(X\right), \operatorname{SimpleGraph}.\operatorname{map}\left((\lambda z:A \mapsto (z:X)), \operatorname{SimpleGraph}.\operatorname{starGraph}\left(a\right)\right)\right), \operatorname{SimpleGraph}.\operatorname{map}\left((\lambda z:B \mapsto (z:X)), \operatorname{SimpleGraph}.\operatorname{starGraph}\left(b\right)\right)\right)))))\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges.conditionI` (`✓ std3`).

*Citation.* Oleksiy Dovgoshey and Olga Rovenska (2026). *On the Graph Corresponding to Center of Distances of Metric Space*. DOI: [10.48550/arXiv.2610.11596](https://doi.org/10.48550/arXiv.2610.11596). URL: <https://arxiv.org/abs/2610.11596v1>.

*Commentary.*

Conjecture 4.2(i) (p. 13): “The diametrical graph G_X is complete bipartite with parts X_1, X_2 satisfying the equality min{|X_1|,|X_2|}=2, and the central graph CG_X is the union G_X with star graphs S_1 and S_2, CG_X=G_X∪ S_1 ∪ S_2, such that V(S_1)=X_1 and V(S_2)=X_2.” Here A and B are the two parts. Their subtype elements a and b are star centers and ensure that both parts are nonempty. Sum.elim embeds the bipartite carrier into X. The two subtype stars are mapped into X, and Max.max is the graph join, with the union of edge sets.

**Definition 1.5 (Conjecture 4.2).**

$$claim \Leftrightarrow \left(\forall X \in Type,\; [\operatorname{Fintype}\left(X\right)] [\operatorname{MetricSpace}\left(X\right)] (\operatorname{IsUltrametricDist}\left(X\right)) \Rightarrow \left((4 \le \operatorname{Fintype}.\operatorname{card}\left(X\right)) \Rightarrow \left((\operatorname{Nat}.\operatorname{card}\left(\operatorname{center}\left(X\right)\right) = 3) \Rightarrow \left(\operatorname{conditionI}\left(X\right) \Leftrightarrow \left(\forall Y \in Type,\; [\operatorname{Fintype}\left(Y\right)] [\operatorname{MetricSpace}\left(Y\right)] (\operatorname{Nat}.\operatorname{card}\left(\operatorname{center}\left(Y\right)\right) = 3) \Rightarrow \left((\operatorname{Fintype}.\operatorname{card}\left(Y\right) = \operatorname{Fintype}.\operatorname{card}\left(X\right)) \Rightarrow \operatorname{Nat}.\operatorname{card}\left((\operatorname{centralGraph}\left(X\right)).edgeSet\right) \le \operatorname{Nat}.\operatorname{card}\left((\operatorname{centralGraph}\left(Y\right)).edgeSet\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges.claim` (`✓ std3`).

*Citation.* Oleksiy Dovgoshey and Olga Rovenska (2026). *On the Graph Corresponding to Center of Distances of Metric Space*. DOI: [10.48550/arXiv.2610.11596](https://doi.org/10.48550/arXiv.2610.11596). URL: <https://arxiv.org/abs/2610.11596v1>.

*Commentary.*

Conjecture 4.2 (p. 13): “Let (X,d) be a finite ultrametric space with |X|≥ 4, let the central graph CG_X be 3-central, and let G_X be the diametrical graph of (X,d). Then the following statements are equivalent. (i) The diametrical graph G_X is complete bipartite with parts X_1, X_2 satisfying the equality min{|X_1|,|X_2|}=2, and the central graph CG_X is the union G_X with star graphs S_1 and S_2, CG_X=G_X∪ S_1 ∪ S_2, such that V(S_1)=X_1 and V(S_2)=X_2. (ii) The inequality |E(CG_X)| ≤ |E(CG_Y)| holds for all metric spaces (Y,ρ) which have 3-central CG_Y and satisfy |Y|=|X|.” X and Y are finite carriers, each equipped with its quantified metric. IsUltrametricDist is assumed only for X. The center has exactly three values, and Nat.card on edgeSet counts unordered edges. The equality of carrier cardinalities imposes no ultrametric restriction on Y.

**Theorem 1.6 (Conjecture 4.2 is false).**

$$\neg (\forall X \in Type,\; [\operatorname{Fintype}\left(X\right)] [\operatorname{MetricSpace}\left(X\right)] (\operatorname{IsUltrametricDist}\left(X\right)) \Rightarrow \left((4 \le \operatorname{Fintype}.\operatorname{card}\left(X\right)) \Rightarrow \left((\operatorname{Nat}.\operatorname{card}\left(\operatorname{center}\left(X\right)\right) = 3) \Rightarrow \left(\operatorname{conditionI}\left(X\right) \Leftrightarrow \left(\forall Y \in Type,\; [\operatorname{Fintype}\left(Y\right)] [\operatorname{MetricSpace}\left(Y\right)] (\operatorname{Nat}.\operatorname{card}\left(\operatorname{center}\left(Y\right)\right) = 3) \Rightarrow \left((\operatorname{Fintype}.\operatorname{card}\left(Y\right) = \operatorname{Fintype}.\operatorname{card}\left(X\right)) \Rightarrow \operatorname{Nat}.\operatorname{card}\left((\operatorname{centralGraph}\left(X\right)).edgeSet\right) \le \operatorname{Nat}.\operatorname{card}\left((\operatorname{centralGraph}\left(Y\right)).edgeSet\right)\right)\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges.result` (`✓ std3`). ∎

*Resolves.* `Problems/central-edges` (refuted) by `D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"central-edges","declaration_gid":"D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Oleksiy Dovgoshey and Olga Rovenska (2026). *On the Graph Corresponding to Center of Distances of Metric Space*. DOI: [10.48550/arXiv.2610.11596](https://doi.org/10.48550/arXiv.2610.11596). URL: <https://arxiv.org/abs/2610.11596v1>.

*Commentary.*

On Fin 4, pull back the 2-adic metric along the values 0,1,2,3. Distinct vertices of the same parity have distance 1/2; opposite parities have distance 1. The center is {0,1/2,1}, the central graph is complete, and its six edges are the union of the diametrical bipartite graph with parts {0,2}, {1,3} and the two single-edge stars. For the comparator, pull back the real metric along 0,4,5,9. Its center is exactly {0,4,5}; its four central edges are {0,1}, {0,2}, {1,3}, {2,3}. The asserted inequality would be 6 ≤ 4. This refutes the implication from (i) to (ii). The comparison restricted to ultrametrics is a separate question.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges.center`
- Truth anchor: `D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges.centralGraph`
- Truth anchor: `D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges.claim`
- Truth anchor: `D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges.conditionI`
- Truth anchor: `D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges.diametricalGraph`
- Truth anchor: `D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges.result`
