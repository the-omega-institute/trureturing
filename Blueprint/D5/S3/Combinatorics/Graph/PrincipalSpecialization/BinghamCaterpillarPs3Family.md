# A family with equal third and unequal second principal specializations

## Abstract

For every positive j, the source caterpillars (5,j,j,4,3) and (4,j,j,5,3) have different second and identical third ordinary chromatic symmetric principal specializations.

**Definition 1.1 (Positive parts).**

$$\forall (l : \mathbb{N}), \operatorname{Parts}\left(l\right) = (\operatorname{Fin}\left(l\right) \to \mathbb{N}^{+})$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarPs3Family.Parts` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aram Bingham, Kyle Celano, Patricia Commins, Rosa Orellana, Jianping Pan, and Mary Claire Simone (2026). *Principal specializations of the t-chromatic symmetric function*. DOI: [10.48550/arXiv.2610.31785](https://doi.org/10.48550/arXiv.2610.31785). URL: <https://arxiv.org/abs/2610.31785v1>.

*Commentary.*

A length-l composition is represented by a function from Fin l to the positive naturals. Fin l uses indices 0 through l−1. The source uses indices 1 through l; adding one identifies the spine indices.

**Definition 1.2 (The source vertex carrier).**

$$\forall (l : \mathbb{N}), \forall (a : \operatorname{Parts}\left(l\right)), \operatorname{Vertex}\left(a\right) = \Sigma_{i:\operatorname{Fin}\left(l\right)} \operatorname{Fin}\left(\operatorname{PNat.val}\left(\operatorname{a}\left(i\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarPs3Family.Vertex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aram Bingham, Kyle Celano, Patricia Commins, Rosa Orellana, Jianping Pan, and Mary Claire Simone (2026). *Principal specializations of the t-chromatic symmetric function*. DOI: [10.48550/arXiv.2610.31785](https://doi.org/10.48550/arXiv.2610.31785). URL: <https://arxiv.org/abs/2610.31785v1>.

*Commentary.*

The dependent pair (i,0) represents the source spine vertex v_(i+1). The pair (i,r), for 1 ≤ r < val(a(i)), represents its leaf w_(i+1,r). Thus the ith block has exactly val(a(i)) vertices. A part equal to one has no leaves.

**Definition 1.3 (The oriented source edge list).**

$$\forall (l : \mathbb{N}), \forall (a : \operatorname{Parts}\left(l\right)), \forall (u : \operatorname{Vertex}\left(a\right)), \forall (v : \operatorname{Vertex}\left(a\right)), \operatorname{edgeRel}\left(a, u, v\right) \Leftrightarrow \left(((u_{1} = v_{1}) \land ((\operatorname{Fin.val}\left(u_{2}\right) = 0) \land (\operatorname{Fin.val}\left(v_{2}\right) \ne 0))) \lor ((\operatorname{Fin.val}\left(u_{2}\right) = 0) \land ((\operatorname{Fin.val}\left(v_{2}\right) = 0) \land (\operatorname{Fin.val}\left(u_{1}\right) + 1 = \operatorname{Fin.val}\left(v_{1}\right))))\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarPs3Family.edgeRel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aram Bingham, Kyle Celano, Patricia Commins, Rosa Orellana, Jianping Pan, and Mary Claire Simone (2026). *Principal specializations of the t-chromatic symmetric function*. DOI: [10.48550/arXiv.2610.31785](https://doi.org/10.48550/arXiv.2610.31785). URL: <https://arxiv.org/abs/2610.31785v1>.

*Commentary.*

Subscripts 1 and 2 denote the two projections of a vertex. The first disjunct lists spine-to-leaf edges inside a block; the second lists forward consecutive spine edges. The val maps are the natural-number projections of Fin elements.

**Definition 1.4 (The caterpillar).**

$$\forall (l : \mathbb{N}), \forall (a : \operatorname{Parts}\left(l\right)), \operatorname{caterpillar}\left(a\right) = \operatorname{SimpleGraph.fromRel}\left(\operatorname{edgeRel}\left(a\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarPs3Family.caterpillar` (`✓ std3`).

*Citation.* Aram Bingham, Kyle Celano, Patricia Commins, Rosa Orellana, Jianping Pan, and Mary Claire Simone (2026). *Principal specializations of the t-chromatic symmetric function*. DOI: [10.48550/arXiv.2610.31785](https://doi.org/10.48550/arXiv.2610.31785). URL: <https://arxiv.org/abs/2610.31785v1>.

*Commentary.*

Mathlib SimpleGraph.fromRel symmetrizes the displayed relation and excludes loops. This is exactly Definition 2.1's caterpillar whenever the source endpoint conditions hold. Both five-part families satisfy those conditions for every positive j. The definition is total on all positive part vectors.

**Definition 1.5 (The ordinary principal specialization).**

$$\forall (V : Type*), [\operatorname{Fintype}\left(V\right)] \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (k : \mathbb{N}), \operatorname{ps}\left(G, k\right) = \sum_{c:\operatorname{SimpleGraph.Coloring}\left(G, \operatorname{Fin}\left(k\right)\right)} \operatorname{Polynomial.X}^{\sum_{v:V} \operatorname{Fin.val}\left(\operatorname{c}\left(v\right)\right)}$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarPs3Family.ps` (`✓ std3`).

*Citation.* Aram Bingham, Kyle Celano, Patricia Commins, Rosa Orellana, Jianping Pan, and Mary Claire Simone (2026). *Principal specializations of the t-chromatic symmetric function*. DOI: [10.48550/arXiv.2610.31785](https://doi.org/10.48550/arXiv.2610.31785). URL: <https://arxiv.org/abs/2610.31785v1>.

*Commentary.*

Equation (2.1) of the source changes to colors 0 through k−1. SimpleGraph.Coloring means every edge has different endpoint colors; it imposes no surjectivity. Every proper coloring into Fin k occurs once in the finite sum. X is Polynomial.X over the integers. These polynomials embed injectively in the source's complex coefficient ring, preserving equality and inequality. No t refinement is used.

**Definition 1.6 (The first family).**

$$\forall (j : \mathbb{N}^{+}), \operatorname{alpha}\left(j\right) = ![5,j,j,4,3]$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarPs3Family.alpha` (`✓ std3`).

*Citation.* Aram Bingham, Kyle Celano, Patricia Commins, Rosa Orellana, Jianping Pan, and Mary Claire Simone (2026). *Principal specializations of the t-chromatic symmetric function*. DOI: [10.48550/arXiv.2610.31785](https://doi.org/10.48550/arXiv.2610.31785). URL: <https://arxiv.org/abs/2610.31785v1>.

*Commentary.*

The tuple denotes the Fin 5 indexed function with the displayed entries, all in the positive naturals.

**Definition 1.7 (The second family).**

$$\forall (j : \mathbb{N}^{+}), \operatorname{beta}\left(j\right) = ![4,j,j,5,3]$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarPs3Family.beta` (`✓ std3`).

*Citation.* Aram Bingham, Kyle Celano, Patricia Commins, Rosa Orellana, Jianping Pan, and Mary Claire Simone (2026). *Principal specializations of the t-chromatic symmetric function*. DOI: [10.48550/arXiv.2610.31785](https://doi.org/10.48550/arXiv.2610.31785). URL: <https://arxiv.org/abs/2610.31785v1>.

*Commentary.*

The repeated internal part is the same arbitrary positive natural j in both positions. The proof uses the fixed end blocks 5,4,3 in the stated algebraic identity.

**Definition 1.8 (Remark 3.11, first question).**

$$claim \Leftrightarrow (\forall (j : \mathbb{N}^{+}), (\operatorname{ps}\left(\operatorname{caterpillar}\left(\operatorname{alpha}\left(j\right)\right), 2\right) \ne \operatorname{ps}\left(\operatorname{caterpillar}\left(\operatorname{beta}\left(j\right)\right), 2\right)) \land (\operatorname{ps}\left(\operatorname{caterpillar}\left(\operatorname{alpha}\left(j\right)\right), 3\right) = \operatorname{ps}\left(\operatorname{caterpillar}\left(\operatorname{beta}\left(j\right)\right), 3\right)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarPs3Family.claim` (`✓ std3`).

*Citation.* Aram Bingham, Kyle Celano, Patricia Commins, Rosa Orellana, Jianping Pan, and Mary Claire Simone (2026). *Principal specializations of the t-chromatic symmetric function*. DOI: [10.48550/arXiv.2610.31785](https://doi.org/10.48550/arXiv.2610.31785). URL: <https://arxiv.org/abs/2610.31785v1>.

*Commentary.*

The domain is all positive integers, including j=1. Equality is formal polynomial equality in Z[X], with an indeterminate X. The second question, whether these are the only such pairs, is outside this statement.

**Theorem 1.9 (The entire positive-parameter family).**

$$\forall (j : \mathbb{N}^{+}), (\operatorname{ps}\left(\operatorname{caterpillar}\left(\operatorname{alpha}\left(j\right)\right), 2\right) \ne \operatorname{ps}\left(\operatorname{caterpillar}\left(\operatorname{beta}\left(j\right)\right), 2\right)) \land (\operatorname{ps}\left(\operatorname{caterpillar}\left(\operatorname{alpha}\left(j\right)\right), 3\right) = \operatorname{ps}\left(\operatorname{caterpillar}\left(\operatorname{beta}\left(j\right)\right), 3\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarPs3Family.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Aram Bingham, Kyle Celano, Patricia Commins, Rosa Orellana, Jianping Pan, and Mary Claire Simone (2026). *Principal specializations of the t-chromatic symmetric function*. DOI: [10.48550/arXiv.2610.31785](https://doi.org/10.48550/arXiv.2610.31785). URL: <https://arxiv.org/abs/2610.31785v1>.

*Commentary.*

Restricting a proper coloring to the spine and its leaves gives a bijection with proper spine colorings and independent leaf assignments. Weight is additive over the actual vertices. Summing the leaf choices gives, for spine color c and positive part a, the block weight X^c times (the sum of X^d over d different from c) raised to val(a)−1. Empty leaf sets contribute one. The five spine colors are then summed subject to consecutive inequality. For three colors, an identity with an arbitrary repeated three-entry middle weight vector interchanges the fixed 5 and 4 blocks while keeping the final 3 block. Polynomial normalization proves that identity before substituting the weights for j, so no finite cutoff on j or numerical evaluation of X occurs. For two colors, the two alternating spine choices give X^(val(j)+5)+X^(val(j)+7) for alpha and X^(val(j)+6)+X^(val(j)+6) for beta. Their coefficients at degree val(j)+5 are one and zero. The proof settles the first question only; classification, the t-chromatic invariant, and the source's four-color conjectures remain outside its scope.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarPs3Family.Parts`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarPs3Family.Vertex`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarPs3Family.alpha`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarPs3Family.beta`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarPs3Family.caterpillar`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarPs3Family.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarPs3Family.edgeRel`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarPs3Family.ps`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarPs3Family.result`
