# Sheffield–Xi Conjecture 1 and its refutation

## Abstract

The icosahedron has five neighbors and five induced edges at every vertex. No abelian Cayley graph has both local counts.

**Definition 1.1 (Triangle regularity).**

$$\forall (V : Type) (G : \operatorname{SimpleGraph}\left(V\right)) (r c : \mathbb{N}), \operatorname{triangleRegular}\left(G, r, c\right) \iff (\forall (v : V), \operatorname{Nat.card}\left(\operatorname{SimpleGraph.neighborSet}\left(G, v\right)\right) = r \land \operatorname{Nat.card}\left(\operatorname{SimpleGraph.edgeSet}\left(\operatorname{SimpleGraph.induce}\left(G, \operatorname{SimpleGraph.neighborSet}\left(G, v\right)\right)\right)\right) = c)$$

*Formalization.* `D5/S3/Combinatorics/Graph/TriangleRegularity/SheffieldXiConjectureOne.triangleRegular` (`✓ std3`).

*Citation.* Nathan S. Sheffield and Zoe Xi (2025). *Graphs With the Same Edge Count in Each Neighborhood*. DOI: [10.48550/arXiv.2507.14473](https://doi.org/10.48550/arXiv.2507.14473). URL: <https://arxiv.org/abs/2507.14473v1>.

*Commentary.*

Every vertex has degree r, and its open neighborhood induces c unordered edges. The second cardinality counts the edge set of the induced simple graph.

**Definition 1.2 (Abelian Cayley realization).**

$$\forall (r c : \mathbb{N}), (\exists (V : Type), \operatorname{Finite}\left(V\right) \land \operatorname{Nonempty}\left(V\right) \land (\exists (G : \operatorname{SimpleGraph}\left(V\right)), \operatorname{triangleRegular}\left(G, r, c\right))) \implies (\exists (B : Type), \operatorname{Finite}\left(B\right) \land (\exists (instB : \operatorname{AddCommGroup}\left(B\right)), \operatorname{letI} : \operatorname{AddCommGroup}\left(B\right) := instB; \exists (S : \operatorname{Set}\left(B\right)), \neg (0 \in S) \land (\forall (x : B), x \in S \implies -x \in S) \land \operatorname{triangleRegular}\left(\operatorname{SimpleGraph.addCayley}\left(S\right), r, c\right)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/TriangleRegularity/SheffieldXiConjectureOne.claim` (`✓ std3`).

*Citation.* Nathan S. Sheffield and Zoe Xi (2025). *Graphs With the Same Edge Count in Each Neighborhood*. DOI: [10.48550/arXiv.2507.14473](https://doi.org/10.48550/arXiv.2507.14473). URL: <https://arxiv.org/abs/2507.14473v1>.

*Commentary.*

Conjecture 1 asks for an abelian Cayley realization of every pair realized by a finite nonempty simple graph. The finite abelian group may have any order. Its connection set is closed under additive inversion and excludes zero. The chosen group structure instB determines both the Cayley adjacency and inversion on B. The display writes the anonymous Finite and Nonempty witnesses as conjunctions.

**Theorem 1.3 (The icosahedral counterexample).**

$$\neg (\forall (r c : \mathbb{N}), (\exists (V : Type), \operatorname{Finite}\left(V\right) \land \operatorname{Nonempty}\left(V\right) \land (\exists (G : \operatorname{SimpleGraph}\left(V\right)), \operatorname{triangleRegular}\left(G, r, c\right))) \implies (\exists (B : Type), \operatorname{Finite}\left(B\right) \land (\exists (instB : \operatorname{AddCommGroup}\left(B\right)), \operatorname{letI} : \operatorname{AddCommGroup}\left(B\right) := instB; \exists (S : \operatorname{Set}\left(B\right)), \neg (0 \in S) \land (\forall (x : B), x \in S \implies -x \in S) \land \operatorname{triangleRegular}\left(\operatorname{SimpleGraph.addCayley}\left(S\right), r, c\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/TriangleRegularity/SheffieldXiConjectureOne.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathan S. Sheffield and Zoe Xi (2025). *Graphs With the Same Edge Count in Each Neighborhood*. DOI: [10.48550/arXiv.2507.14473](https://doi.org/10.48550/arXiv.2507.14473). URL: <https://arxiv.org/abs/2507.14473v1>.

*Commentary.*

Use the icosahedral graph on two poles and two rings of five vertices. Every open neighborhood has five vertices and five edges. Caro and Mifsud give a twelve-vertex planar (5,5)-realization in Figure 5. Hak and coauthors identify the icosahedron as their graph G1 in Appendix A.

In an abelian Cayley graph, the open neighborhood of zero is the connection set. Each oriented edge from x to y there corresponds to the ordered zero-sum triple (x, y − x, −y). Five unordered edges would give ten triples. Rotation counts those triples modulo three by their diagonal fixed points. Negation pairs the nonzero connection elements killed by three. In a five-element connection set the two congruences force exactly four such elements.

The remaining element equals its negative and cannot occur in a zero-sum triple. Among the four elements killed by three, a repeated coordinate forces all three coordinates to agree. Three distinct coordinates cannot contain an opposite pair, since the third coordinate would then be zero. The four elements form two opposite pairs, so three distinct coordinates would have to contain such a pair. Only the four diagonal triples remain, contradicting the count of ten.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/TriangleRegularity/SheffieldXiConjectureOne.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/TriangleRegularity/SheffieldXiConjectureOne.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/TriangleRegularity/SheffieldXiConjectureOne.triangleRegular`
