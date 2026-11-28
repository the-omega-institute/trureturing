# A disconnected proper generalized power graph

## Abstract

A torsion group with cyclic center has a disconnected proper generalized power graph.

The vertices of P(G) are the nonidentity elements of G. Distinct vertices x and y are adjacent if a finite list of elements g of G gives y as the ordered product of g⁻¹xg, or gives x as the ordered product of g⁻¹yg. The empty product is the identity and hence cannot produce a proper vertex.

**Definition 1.1 (The torsion-group assertion).**

$$\operatorname{claim} = (\forall G \in \operatorname{Type},\; [\operatorname{Group}\left(G\right)] (\forall x \in G,\; \operatorname{IsOfFinOrder}\left(x\right)) \Rightarrow \left(\operatorname{IsCyclic}\left(\operatorname{Z}\left(G\right)\right) \Rightarrow (\operatorname{Connected}\left(\operatorname{P}\left(G\right)\right) \land \operatorname{ediam}\left(\operatorname{P}\left(G\right)\right) \le 4)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/PowerGraphs/SilveiraContrerasTorsionRefutation.claim` (`✓ std3`).

*Citation.* Danilo Silveira and Yerko Contreras Rojas (2026). *Generalized Power Graph of a group*. DOI: [10.48550/arXiv.2611.17525](https://doi.org/10.48550/arXiv.2611.17525). URL: <https://arxiv.org/abs/2611.17525v1>.

*Commentary.*

Problem 4.3 asks whether Theorem 4.2(2) remains true with torsion in place of finiteness. Here torsion means every element has finite order, Z(G) is the group center, and the extended diameter is the supremum of pairwise extended graph distances.

**Theorem 1.2 (Refutation by an isolated central involution).**

$$\neg (\forall G \in \operatorname{Type},\; [\operatorname{Group}\left(G\right)] (\forall x \in G,\; \operatorname{IsOfFinOrder}\left(x\right)) \Rightarrow \left(\operatorname{IsCyclic}\left(\operatorname{Z}\left(G\right)\right) \Rightarrow (\operatorname{Connected}\left(\operatorname{P}\left(G\right)\right) \land \operatorname{ediam}\left(\operatorname{P}\left(G\right)\right) \le 4)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PowerGraphs/SilveiraContrerasTorsionRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/silveira-contreras-2026-torsion-powergraph` (refuted) by `D5/S3/Combinatorics/Graph/PowerGraphs/SilveiraContrerasTorsionRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"silveira-contreras-2026-torsion-powergraph","declaration_gid":"D5/S3/Combinatorics/Graph/PowerGraphs/SilveiraContrerasTorsionRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Danilo Silveira and Yerko Contreras Rojas (2026). *Generalized Power Graph of a group*. DOI: [10.48550/arXiv.2611.17525](https://doi.org/10.48550/arXiv.2611.17525). URL: <https://arxiv.org/abs/2611.17525v1>.

*Commentary.*

Start with the trivial group and iterate regular wreath products by C₂. Embed each stage in the coordinate indexed by the identity. Each stage is a finite 2-group, so every element of the direct limit H has finite order. In the next stage the nonidentity shift moves every embedded nonidentity element. Since the stage maps are injective, the shifted element is distinct in H, so H has trivial center.

For a nonidentity a in H, lift a and a finite list of conjugators to one stage. In that finite 2-group, pass to the quotient by the first lower central series term omitting a. The image of a is central, nonidentity, and of even order. The product of an odd number of conjugates has image an odd power of a's image and cannot equal the identity.

The center of H × C₂ is the second factor. Let c be the nonidentity element of C₂. Products of conjugates of (1,c) are powers of (1,c), giving no outgoing edge. A product from a distinct proper vertex to (1,c) would have to start with a vertex (a,c) and have odd length by its second coordinate. Its first coordinate would give an odd product of conjugates of a ≠ 1 equal to the identity. Thus (1,c) has no incoming edge either. The image of the first-stage shift, paired with 1, is a second proper vertex. A walk to it would require a first edge at (1,c).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PowerGraphs/SilveiraContrerasTorsionRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/PowerGraphs/SilveiraContrerasTorsionRefutation.result`
