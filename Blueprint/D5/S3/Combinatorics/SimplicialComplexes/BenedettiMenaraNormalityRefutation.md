# Flag completion can destroy normality without changing pure dimension

## Abstract

A ten-vertex complex refutes normality preservation under flag completion.

**Definition 1.1 (Pure rank).**

$$\forall n \in \mathbb{N},\; \forall K \in \operatorname{AbstractSimplicialComplex}\left(\operatorname{Fin}\left(n\right)\right),\; \forall d \in \mathbb{N},\; \operatorname{Pure}\left(K, d\right) = \left((\exists F \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; (F \in K) \land (\forall T \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; (T \in K) \Rightarrow ((F \subseteq T) \Rightarrow (T = F)))) \land (\forall F \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; ((F \in K) \land (\forall T \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; (T \in K) \Rightarrow ((F \subseteq T) \Rightarrow (T = F)))) \Rightarrow (\operatorname{Finset}.\operatorname{card}\left(F\right) = d))\right)$$

*Formalization.* `D5/S3/Combinatorics/SimplicialComplexes/BenedettiMenaraNormalityRefutation.Pure` (`✓ std3`).

*Citation.* Bruno Benedetti and Giuliamaria Menara (2026). *Diameter bounds for complexes that are close to flag or close to normal*. DOI: [10.48550/arXiv.2611.08071](https://doi.org/10.48550/arXiv.2611.08071). URL: <https://arxiv.org/abs/2611.08071v1>.

*Commentary.*

Page 7: Throughout, Δ is a (finite) pure simplicial complex of dimension d − 1 on a vertex set V with |V| = n. A facet is a nonempty face maximal under inclusion. Pure K d requires a facet to exist and every facet to have exactly d vertices, so the dimension is d - 1.

**Definition 1.2 (The dual graph).**

$$\forall n \in \mathbb{N},\; \forall K \in \operatorname{AbstractSimplicialComplex}\left(\operatorname{Fin}\left(n\right)\right),\; \forall d \in \mathbb{N},\; \operatorname{dualGraph}\left(K, d\right) = \operatorname{SimpleGraph}.\operatorname{fromRel}\left((\operatorname{fun} (F:\operatorname{Subtype}\left((\operatorname{fun} (F:\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)) \mapsto (F \in K) \land (\forall T \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; (T \in K) \Rightarrow ((F \subseteq T) \Rightarrow (T = F))))\right)) \mapsto \operatorname{fun} (H:\operatorname{Subtype}\left((\operatorname{fun} (F:\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)) \mapsto (F \in K) \land (\forall T \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; (T \in K) \Rightarrow ((F \subseteq T) \Rightarrow (T = F))))\right)) \mapsto \operatorname{Finset}.\operatorname{card}\left((\operatorname{Finset}.\operatorname{inter}\left(\operatorname{val}\left(F\right), \operatorname{val}\left(H\right)\right))\right) + 1 = d)\right)$$

*Formalization.* `D5/S3/Combinatorics/SimplicialComplexes/BenedettiMenaraNormalityRefutation.dualGraph` (`✓ std3`).

*Citation.* Bruno Benedetti and Giuliamaria Menara (2026). *Diameter bounds for complexes that are close to flag or close to normal*. DOI: [10.48550/arXiv.2611.08071](https://doi.org/10.48550/arXiv.2611.08071). URL: <https://arxiv.org/abs/2611.08071v1>.

*Commentary.*

Page 7: The dual graph 𝒢(Δ) has the facets of Δ as nodes, and its edges join facets that are adjacent, i.e. that share exactly d − 1 vertices; diam(Δ) is its diameter. SimpleGraph.fromRel excludes equality of its vertices and symmetrizes the displayed intersection condition.

**Definition 1.3 (Normality of all face-stars).**

$$\forall n \in \mathbb{N},\; \forall K \in \operatorname{AbstractSimplicialComplex}\left(\operatorname{Fin}\left(n\right)\right),\; \forall d \in \mathbb{N},\; \operatorname{Normal}\left(K, d\right) = \left(\forall sigma \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; (\operatorname{D5}.\operatorname{S3}.\operatorname{Geometry}.\operatorname{FiniteRelativeSimplicialCollapse}.\operatorname{AugmentedFace}\left(\operatorname{AbstractSimplicialComplex}.\operatorname{toPreAbstractSimplicialComplex}\left(K\right), sigma\right)) \Rightarrow (\operatorname{SimpleGraph}.\operatorname{Connected}\left(\operatorname{SimpleGraph}.\operatorname{induce}\left(\{F:\operatorname{Subtype}\left((\operatorname{fun} (F:\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)) \mapsto (F \in K) \land (\forall T \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; (T \in K) \Rightarrow ((F \subseteq T) \Rightarrow (T = F))))\right) | sigma \subseteq \operatorname{val}\left(F\right)\}, \operatorname{dualGraph}\left(K, d\right)\right)\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/SimplicialComplexes/BenedettiMenaraNormalityRefutation.Normal` (`✓ std3`).

*Citation.* Bruno Benedetti and Giuliamaria Menara (2026). *Diameter bounds for complexes that are close to flag or close to normal*. DOI: [10.48550/arXiv.2611.08071](https://doi.org/10.48550/arXiv.2611.08071). URL: <https://arxiv.org/abs/2611.08071v1>.

*Commentary.*

Page 1: The question is typically asked for normal complexes, i.e. complexes Δ where for every face σ, including the empty one, the facets containing σ induce a connected subgraph of 𝒢(Δ). The graph is induced on its own subtype of facets containing sigma. Connected includes nonemptiness.

**Definition 1.4 (The one-skeleton).**

$$\forall n \in \mathbb{N},\; \forall K \in \operatorname{AbstractSimplicialComplex}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{skeleton}\left(K\right) = \operatorname{SimpleGraph}.\operatorname{fromRel}\left((\operatorname{fun} (u:\operatorname{Fin}\left(n\right)) \mapsto \operatorname{fun} (v:\operatorname{Fin}\left(n\right)) \mapsto (\{u,v\}:\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)) \in K)\right)$$

*Formalization.* `D5/S3/Combinatorics/SimplicialComplexes/BenedettiMenaraNormalityRefutation.skeleton` (`✓ std3`).

*Citation.* Bruno Benedetti and Giuliamaria Menara (2026). *Diameter bounds for complexes that are close to flag or close to normal*. DOI: [10.48550/arXiv.2611.08071](https://doi.org/10.48550/arXiv.2611.08071). URL: <https://arxiv.org/abs/2611.08071v1>.

*Commentary.*

The vertices are all of Fin n. Distinct u and v are adjacent exactly when their two-element set is a face. Singletons are present in every AbstractSimplicialComplex.

**Definition 1.5 (The gap in minimal nonfaces).**

$$\forall n \in \mathbb{N},\; \forall K \in \operatorname{AbstractSimplicialComplex}\left(\operatorname{Fin}\left(n\right)\right),\; \forall d \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{Gap}\left(K, d, k\right) = \left(\forall M \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; ((\neg \operatorname{D5}.\operatorname{S3}.\operatorname{Geometry}.\operatorname{FiniteRelativeSimplicialCollapse}.\operatorname{AugmentedFace}\left(\operatorname{AbstractSimplicialComplex}.\operatorname{toPreAbstractSimplicialComplex}\left(K\right), M\right)) \land (\forall T \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; (T \subset M) \Rightarrow (\operatorname{D5}.\operatorname{S3}.\operatorname{Geometry}.\operatorname{FiniteRelativeSimplicialCollapse}.\operatorname{AugmentedFace}\left(\operatorname{AbstractSimplicialComplex}.\operatorname{toPreAbstractSimplicialComplex}\left(K\right), T\right)))) \Rightarrow (\neg ((3 \le \operatorname{Finset}.\operatorname{card}\left(M\right)) \land (\operatorname{Finset}.\operatorname{card}\left(M\right) + k \le d)))\right)$$

*Formalization.* `D5/S3/Combinatorics/SimplicialComplexes/BenedettiMenaraNormalityRefutation.Gap` (`✓ std3`).

*Citation.* Bruno Benedetti and Giuliamaria Menara (2026). *Diameter bounds for complexes that are close to flag or close to normal*. DOI: [10.48550/arXiv.2611.08071](https://doi.org/10.48550/arXiv.2611.08071). URL: <https://arxiv.org/abs/2611.08071v1>.

*Commentary.*

Page 2: Δ has no minimal nonfaces of size 3, 4, …, d − k. A minimal nonface is not an augmented face and all of its proper subsets are augmented faces. Under k + 2 <= d, the forbidden upper bound is expressed without subtraction as M.card + k <= d. At d = 4 and k = 2 the forbidden interval is empty.

**Definition 1.6 (Question 9.1).**

$$\operatorname{claim} = \left(\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall K \in \operatorname{AbstractSimplicialComplex}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{let} C:=(\{\operatorname{faces}:=\{s | (\operatorname{Finset}.\operatorname{Nonempty}\left(s\right)) \land (\operatorname{SimpleGraph}.\operatorname{IsClique}\left(\operatorname{skeleton}\left(K\right), (s:\operatorname{Set}\left(\operatorname{Fin}\left(n\right)\right))\right))\}\}:\operatorname{AbstractSimplicialComplex}\left(\operatorname{Fin}\left(n\right)\right)); (2 \le k) \Rightarrow ((k + 2 \le d) \Rightarrow ((\operatorname{Pure}\left(K, d\right)) \Rightarrow ((\operatorname{Normal}\left(K, d\right)) \Rightarrow ((\operatorname{Gap}\left(K, d, k\right)) \Rightarrow ((\operatorname{Pure}\left(C, d\right)) \Rightarrow (\operatorname{Normal}\left(C, d\right)))))))\right)$$

*Formalization.* `D5/S3/Combinatorics/SimplicialComplexes/BenedettiMenaraNormalityRefutation.claim` (`✓ std3`).

*Citation.* Bruno Benedetti and Giuliamaria Menara (2026). *Diameter bounds for complexes that are close to flag or close to normal*. DOI: [10.48550/arXiv.2611.08071](https://doi.org/10.48550/arXiv.2611.08071). URL: <https://arxiv.org/abs/2611.08071v1>.

*Commentary.*

Page 21, Question 9.1: In Main Theorem A with k ≥ 2, does normality of Δ̂ follow from normality of Δ together with (Gₖ) and purity of Δ̂? (For k ≤ 1 it does, by Proposition 3.5.) The vertex carrier is Fin n, d is facet cardinality and k satisfies 2 <= k and k + 2 <= d. C is the complex whose nonempty faces are the cliques of skeleton K. Every vertex occurs, and AugmentedFace includes the empty face. Page 2: Let now Δ̂ be the flag completion of Δ, that is, the clique complex of its 1-skeleton. In the displayed record the fields proving downward closure and singleton membership are determined by the clique condition.

**Theorem 1.7 (Refutation of Question 9.1).**

$$\neg (\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall K \in \operatorname{AbstractSimplicialComplex}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{let} C:=(\{\operatorname{faces}:=\{s | (\operatorname{Finset}.\operatorname{Nonempty}\left(s\right)) \land (\operatorname{SimpleGraph}.\operatorname{IsClique}\left(\operatorname{skeleton}\left(K\right), (s:\operatorname{Set}\left(\operatorname{Fin}\left(n\right)\right))\right))\}\}:\operatorname{AbstractSimplicialComplex}\left(\operatorname{Fin}\left(n\right)\right)); (2 \le k) \Rightarrow ((k + 2 \le d) \Rightarrow ((\operatorname{Pure}\left(K, d\right)) \Rightarrow ((\operatorname{Normal}\left(K, d\right)) \Rightarrow ((\operatorname{Gap}\left(K, d, k\right)) \Rightarrow ((\operatorname{Pure}\left(C, d\right)) \Rightarrow (\operatorname{Normal}\left(C, d\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SimplicialComplexes/BenedettiMenaraNormalityRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bruno Benedetti and Giuliamaria Menara (2026). *Diameter bounds for complexes that are close to flag or close to normal*. DOI: [10.48550/arXiv.2611.08071](https://doi.org/10.48550/arXiv.2611.08071). URL: <https://arxiv.org/abs/2611.08071v1>.

*Commentary.*

Take n = 10, d = 4 and k = 2, with a = 6, z = 7, w = 8 and b = 9. The original facets, in order, are zw01, zw12, zw23, zw34, zw45, zw50, az01, az12, az23, az34, wb01, wb50, wb45, wb34 and ab01. Each has four vertices and every vertex occurs. For any two facets at distinct positions, their intersection is contained in an earlier facet meeting the later one in three vertices. Strong induction on the sum of the positions constructs a path between every two facets containing a given face, including the empty face. Thus the original complex is normal. The completion has precisely these facets and ab34, and remains pure of rank four. Its ab-star consists of ab01 and ab34, whose intersection has two vertices; its induced dual graph has two vertices and no edges. Consequently the completion is not normal.

The gap condition here is vacuous, as the source allows at k = d - 2. Proposition 3.5 for k <= 1 and Main Theorem A, which assumes completion normality, retain their stated hypotheses. This example leaves preservation under nonvacuous G_k with 2 <= k < d - 2 and the uniform arbitrary-N family as separate questions.

## References

- Truth anchor: `D5/S3/Combinatorics/SimplicialComplexes/BenedettiMenaraNormalityRefutation.Gap`
- Truth anchor: `D5/S3/Combinatorics/SimplicialComplexes/BenedettiMenaraNormalityRefutation.Normal`
- Truth anchor: `D5/S3/Combinatorics/SimplicialComplexes/BenedettiMenaraNormalityRefutation.Pure`
- Truth anchor: `D5/S3/Combinatorics/SimplicialComplexes/BenedettiMenaraNormalityRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/SimplicialComplexes/BenedettiMenaraNormalityRefutation.dualGraph`
- Truth anchor: `D5/S3/Combinatorics/SimplicialComplexes/BenedettiMenaraNormalityRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/SimplicialComplexes/BenedettiMenaraNormalityRefutation.skeleton`
- Dependency: [D5/S3/Geometry/FiniteAlexanderDualCollapse](../../Geometry/FiniteAlexanderDualCollapse.md)
- Dependency: [D5/S3/Geometry/FiniteGraphVertexSubstitution](../../Geometry/FiniteGraphVertexSubstitution.md)
- Dependency: [D5/S3/Geometry/FiniteRelativeSimplicialCollapse](../../Geometry/FiniteRelativeSimplicialCollapse.md)
