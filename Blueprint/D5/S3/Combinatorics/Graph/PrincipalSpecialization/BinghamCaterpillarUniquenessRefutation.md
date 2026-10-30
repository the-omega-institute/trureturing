# A counterexample to the exhaustive-pairs assertion

## Abstract

The eighteen-vertex caterpillars (2,2,2,2,2,1,4,3) and (2,2,3,2,3,4,2) refute the second, exhaustive-pairs question in Remark 3.11.

**Definition 1.1 (The entire source domain).**

$$\forall (l:\mathbb{N}), \forall (a:\operatorname{Parts}\left(l\right)), \operatorname{admissible}\left(a\right) \Leftrightarrow (((l = 1) \land (\forall (i:\operatorname{Fin}\left(l\right)), \operatorname{a}\left(i\right) = 1)) \lor ((1 \le l) \land (\forall (i:\operatorname{Fin}\left(l\right)), ((\operatorname{val}\left(i\right) = 0) \lor (\operatorname{val}\left(i\right) + 1 = l)) \Rightarrow (2 \le \operatorname{val}\left(\operatorname{a}\left(i\right)\right)))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.admissible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aram Bingham, Kyle Celano, Patricia Commins, Rosa Orellana, Jianping Pan, and Mary Claire Simone (2026). *Principal specializations of the t-chromatic symmetric function*. DOI: [10.48550/arXiv.2610.31785](https://doi.org/10.48550/arXiv.2610.31785). URL: <https://arxiv.org/abs/2610.31785v1>.

*Commentary.*

The entries of a are positive naturals indexed by Fin l. The first disjunct is the singleton (1). The second allows every nonempty length whose first and last parts are at least two, including length-one stars. For length one the same part is both endpoints. Positive entries and the endpoint condition imply total size at least two. This is Definition 2.1; Lemma 2.2 is not needed.

**Definition 1.2 (The actual ordinary specialization over C).**

$$\forall (V:Type*), [\operatorname{Fintype}\left(V\right)] \forall (G:\operatorname{SimpleGraph}\left(V\right)), \forall (k:\mathbb{N}), \operatorname{ordinary}\left(G, k\right) = \sum_{c:\operatorname{Coloring}\left(G, \operatorname{Fin}\left(k\right)\right)} X^{\sum_{v:V} \operatorname{val}\left(\operatorname{c}\left(v\right)\right)}$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.ordinary` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aram Bingham, Kyle Celano, Patricia Commins, Rosa Orellana, Jianping Pan, and Mary Claire Simone (2026). *Principal specializations of the t-chromatic symmetric function*. DOI: [10.48550/arXiv.2610.31785](https://doi.org/10.48550/arXiv.2610.31785). URL: <https://arxiv.org/abs/2610.31785v1>.

*Commentary.*

G is any finite simple graph on V. The sum includes every proper coloring into Fin k, without surjectivity. Equation (2.1) changes the color names to 0 through k−1; the exponent is the sum over all actual vertices. The identity ordinary G k = Polynomial.map (Int.castRingHom C) (ps G k) uses ps from BinghamCaterpillarPs3Family. Injectivity of the integer coefficient inclusion makes equality of these complex polynomials equivalent to equality of the integer coloring-count polynomials. No numerical evaluation or t refinement is involved.

**Definition 1.3 (Unordered graph-isomorphism pairs).**

$$\forall (la:\mathbb{N}), \forall (lb:\mathbb{N}), \forall (lc:\mathbb{N}), \forall (ld:\mathbb{N}), \forall (a:\operatorname{Parts}\left(la\right)), \forall (b:\operatorname{Parts}\left(lb\right)), \forall (c:\operatorname{Parts}\left(lc\right)), \forall (d:\operatorname{Parts}\left(ld\right)), \operatorname{pairIso}\left(a, b, c, d\right) \Leftrightarrow (((\operatorname{Iso}\left(a, c\right)) \land (\operatorname{Iso}\left(b, d\right))) \lor ((\operatorname{Iso}\left(a, d\right)) \land (\operatorname{Iso}\left(b, c\right))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.pairIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aram Bingham, Kyle Celano, Patricia Commins, Rosa Orellana, Jianping Pan, and Mary Claire Simone (2026). *Principal specializations of the t-chromatic symmetric function*. DOI: [10.48550/arXiv.2610.31785](https://doi.org/10.48550/arXiv.2610.31785). URL: <https://arxiv.org/abs/2610.31785v1>.

*Commentary.*

Iso(a,c) abbreviates Nonempty (caterpillar a ≃g caterpillar c). The carrier and edge relation are the original Vertex and caterpillar definitions from BinghamCaterpillarPs3Family: a spine path with val(a(i))−1 attached leaves. Graph isomorphisms allow arbitrary relabeling, so this relation includes reversals and both pair orders. No classification of graph isomorphisms by reversed compositions is assumed.

**Definition 1.4 (The first base member).**

$$\operatorname{baseA} = ![5,4,3]$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.baseA` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aram Bingham, Kyle Celano, Patricia Commins, Rosa Orellana, Jianping Pan, and Mary Claire Simone (2026). *Principal specializations of the t-chromatic symmetric function*. DOI: [10.48550/arXiv.2610.31785](https://doi.org/10.48550/arXiv.2610.31785). URL: <https://arxiv.org/abs/2610.31785v1>.

*Commentary.*

The base pair displayed in Remark 3.11.

**Definition 1.5 (The second base member).**

$$\operatorname{baseB} = ![4,5,3]$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.baseB` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aram Bingham, Kyle Celano, Patricia Commins, Rosa Orellana, Jianping Pan, and Mary Claire Simone (2026). *Principal specializations of the t-chromatic symmetric function*. DOI: [10.48550/arXiv.2610.31785](https://doi.org/10.48550/arXiv.2610.31785). URL: <https://arxiv.org/abs/2610.31785v1>.

*Commentary.*

Both base compositions have three spine vertices.

**Definition 1.6 (All listed exceptions).**

$$\forall (la:\mathbb{N}), \forall (lb:\mathbb{N}), \forall (a:\operatorname{Parts}\left(la\right)), \forall (b:\operatorname{Parts}\left(lb\right)), \operatorname{listed}\left(a, b\right) \Leftrightarrow ((\operatorname{pairIso}\left(a, b, \operatorname{baseA}, \operatorname{baseB}\right)) \lor (\exists (j:\mathbb{N}^{+}), \operatorname{pairIso}\left(a, b, \operatorname{alpha}\left(j\right), \operatorname{beta}\left(j\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.listed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aram Bingham, Kyle Celano, Patricia Commins, Rosa Orellana, Jianping Pan, and Mary Claire Simone (2026). *Principal specializations of the t-chromatic symmetric function*. DOI: [10.48550/arXiv.2610.31785](https://doi.org/10.48550/arXiv.2610.31785). URL: <https://arxiv.org/abs/2610.31785v1>.

*Commentary.*

The positive natural j has no upper bound; alpha(j)=(5,j,j,4,3) and beta(j)=(4,j,j,5,3) are reused from the first-question module. In particular j=1 remains included. Pair isomorphism takes the full unordered isomorphism closure of the base and every family pair.

**Definition 1.7 (Remark 3.11, the whole second assertion).**

$$claim \Leftrightarrow (\forall (n:\mathbb{N}), (1 \le n) \Rightarrow (\forall (la:\mathbb{N}), \forall (lb:\mathbb{N}), \forall (a:\operatorname{Parts}\left(la\right)), \forall (b:\operatorname{Parts}\left(lb\right)), ((\operatorname{admissible}\left(a\right)) \land ((\operatorname{admissible}\left(b\right)) \land ((\sum_{i} \operatorname{val}\left(\operatorname{a}\left(i\right)\right) = n) \land ((\sum_{i} \operatorname{val}\left(\operatorname{b}\left(i\right)\right) = n) \land ((\operatorname{ordinary}\left(\operatorname{caterpillar}\left(a\right), 2\right) \ne \operatorname{ordinary}\left(\operatorname{caterpillar}\left(b\right), 2\right)) \land (\operatorname{ordinary}\left(\operatorname{caterpillar}\left(a\right), 3\right) = \operatorname{ordinary}\left(\operatorname{caterpillar}\left(b\right), 3\right))))))) \Rightarrow (\operatorname{listed}\left(a, b\right))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aram Bingham, Kyle Celano, Patricia Commins, Rosa Orellana, Jianping Pan, and Mary Claire Simone (2026). *Principal specializations of the t-chromatic symmetric function*. DOI: [10.48550/arXiv.2610.31785](https://doi.org/10.48550/arXiv.2610.31785). URL: <https://arxiv.org/abs/2610.31785v1>.

*Commentary.*

n ranges over every natural number at least one; la and lb are arbitrary natural lengths. The two compositions are source-admissible and each has total size n. If their ordinary second polynomials differ and third polynomials agree identically, the assertion says their unordered graph-isomorphism pair is listed. The base exception and every positive-j family are included. This is an assertion over all sizes, not a finite search bound.

**Definition 1.8 (The first witness).**

$$\operatorname{witnessA} = ![2,2,2,2,2,1,4,3]$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.witnessA` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aram Bingham, Kyle Celano, Patricia Commins, Rosa Orellana, Jianping Pan, and Mary Claire Simone (2026). *Principal specializations of the t-chromatic symmetric function*. DOI: [10.48550/arXiv.2610.31785](https://doi.org/10.48550/arXiv.2610.31785). URL: <https://arxiv.org/abs/2610.31785v1>.

*Commentary.*

The eight positive parts sum to eighteen and both endpoints are at least two. The internal part one has no attached leaves; its spine vertex still has its two spine neighbors.

**Definition 1.9 (The second witness).**

$$\operatorname{witnessB} = ![2,2,3,2,3,4,2]$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.witnessB` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aram Bingham, Kyle Celano, Patricia Commins, Rosa Orellana, Jianping Pan, and Mary Claire Simone (2026). *Principal specializations of the t-chromatic symmetric function*. DOI: [10.48550/arXiv.2610.31785](https://doi.org/10.48550/arXiv.2610.31785). URL: <https://arxiv.org/abs/2610.31785v1>.

*Commentary.*

The seven positive parts sum to eighteen and satisfy the same endpoint condition.

**Theorem 1.10 (The exhaustive-pairs assertion is false).**

$$\neg(\forall (n:\mathbb{N}), (1 \le n) \Rightarrow (\forall (la:\mathbb{N}), \forall (lb:\mathbb{N}), \forall (a:\operatorname{Parts}\left(la\right)), \forall (b:\operatorname{Parts}\left(lb\right)), ((\operatorname{admissible}\left(a\right)) \land ((\operatorname{admissible}\left(b\right)) \land ((\sum_{i} \operatorname{val}\left(\operatorname{a}\left(i\right)\right) = n) \land ((\sum_{i} \operatorname{val}\left(\operatorname{b}\left(i\right)\right) = n) \land ((\operatorname{ordinary}\left(\operatorname{caterpillar}\left(a\right), 2\right) \ne \operatorname{ordinary}\left(\operatorname{caterpillar}\left(b\right), 2\right)) \land (\operatorname{ordinary}\left(\operatorname{caterpillar}\left(a\right), 3\right) = \operatorname{ordinary}\left(\operatorname{caterpillar}\left(b\right), 3\right))))))) \Rightarrow (\operatorname{listed}\left(a, b\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/bingham-2026-caterpillar-principal-specialization-uniqueness` (refuted) by `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bingham-2026-caterpillar-principal-specialization-uniqueness","declaration_gid":"D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Aram Bingham, Kyle Celano, Patricia Commins, Rosa Orellana, Jianping Pan, and Mary Claire Simone (2026). *Principal specializations of the t-chromatic symmetric function*. DOI: [10.48550/arXiv.2610.31785](https://doi.org/10.48550/arXiv.2610.31785). URL: <https://arxiv.org/abs/2610.31785v1>.

*Commentary.*

For A=witnessA and B=witnessB, the actual two-color polynomials are X^8+X^10 and 2X^9. The coefficients at degree eight are one and zero. Their actual three-color polynomials agree. The identity ps_spine_sum follows from the explicit bijection between all proper colorings and proper spine colorings with independent leaf choices. Each block has weight X^c times (the sum of X^d over d different from c) to the power val(a(i))−1. Finite spine sums and polynomial normalization prove the two identities and the complete third-polynomial equality. The injective coefficient-extension bridge transfers both comparisons to the source's complex polynomials. To exclude every listed pair, a vertex with two distinct neighbors must lie on the spine: a pendant vertex has its incident spine vertex as its only neighbor. Every one of A's eight spine vertices has two distinct neighbors. Any graph isomorphism from A to a caterpillar with l spine vertices would therefore induce an injection Fin 8 into Fin l. Each base member has l=3 and each family member has l=5 for every positive j. The resulting cardinal inequalities exclude every such isomorphism, including all relabelings, reversals, and pair exchanges. This single pair refutes the full universal assertion. It asserts no minimality, priority, converse classification, four-color statement, or t-refined extension.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.admissible`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.baseA`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.baseB`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.listed`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.ordinary`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.pairIso`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.witnessA`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.witnessB`
- Dependency: [D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarPs3Family](BinghamCaterpillarPs3Family.md)
