# The full graph and source convention

## Abstract

Full commuting graphs use whole-element distinctness, and source-derived groups use the inverse-first commutator.

**Definition 1.1 (All elements are vertices).**

$$\forall G \in \operatorname{Type}\left(\right),\; [\operatorname{Group}\left(G\right)] \forall x \in G,\; \forall y \in G,\; \operatorname{Adj}\left(\operatorname{commutingGraph}\left(G\right), x, y\right) = \left((x \ne y) \land (\operatorname{mul}\left(x, y\right) = \operatorname{mul}\left(y, x\right))\right)$$

*Formalization.* `D5/S3/FiniteGroups/Heisenberg/CommutingGraph.commutingGraph` (`✓ std3`).

*Citation.* V. Arvind, Peter J. Cameron, Xuanlong Ma and Natalia V. Maslova (2023). *Aspects of the commuting graph*. DOI: [10.48550/arXiv.2305.07301](https://doi.org/10.48550/arXiv.2305.07301). URL: <https://arxiv.org/abs/2305.07301v5>.

*Commentary.*

The vertex type is the entire group G. Adjacency is the conjunction x distinct from y and x*y=y*x. In particular the identity and every centre element are retained. The simple graph has no loops; distinct elements that differ only in a central coordinate remain eligible for adjacency.

**Definition 1.2 (Isoclinism intertwines the source commutators).**

$$\forall G \in \operatorname{Type}\left(\right),\; \forall H \in \operatorname{Type}\left(\right),\; [\operatorname{Group}\left(G\right)] [\operatorname{Group}\left(H\right)] \operatorname{Isoclinic}\left(G, H\right) = \left(\exists a \in \operatorname{MulEquiv}\left(\operatorname{CentralQuotient}\left(G\right), \operatorname{CentralQuotient}\left(H\right)\right),\; \exists b \in \operatorname{MulEquiv}\left(\operatorname{sourceDerived}\left(G\right), \operatorname{sourceDerived}\left(H\right)\right),\; \forall x \in G,\; \forall y \in G,\; \forall u \in H,\; \forall v \in H,\; (\operatorname{apply}\left(a, \operatorname{Coset}\left(x\right)\right) = \operatorname{Coset}\left(u\right)) \Rightarrow ((\operatorname{apply}\left(a, \operatorname{Coset}\left(y\right)\right) = \operatorname{Coset}\left(v\right)) \Rightarrow (\operatorname{apply}\left(b, \operatorname{sourceCommutator}\left(x, y\right)\right) = \operatorname{sourceCommutator}\left(u, v\right)))\right)$$

*Formalization.* `D5/S3/FiniteGroups/Heisenberg/CommutingGraph.Isoclinic` (`✓ std3`).

*Citation.* V. Arvind, Peter J. Cameron, Xuanlong Ma and Natalia V. Maslova (2023). *Aspects of the commuting graph*. DOI: [10.48550/arXiv.2305.07301](https://doi.org/10.48550/arXiv.2305.07301). URL: <https://arxiv.org/abs/2305.07301v5>.

*Commentary.*

sourceCommutator(x,y) is x inverse times y inverse times x times y. sourceDerived is the subgroup closure of all these commutators. Isoclinic G H asserts the existence of a group isomorphism a from G modulo its centre to H modulo its centre and a group isomorphism b of the source derived subgroups. For every x,y in G and every u,v in H representing a(xZ(G)) and a(yZ(G)), the image under b of sourceCommutator(x,y) equals sourceCommutator(u,v). The commutator is coerced into the ambient group in this equality. This retains compatibility for all representatives, rather than comparing derived groups alone.

**Theorem 1.3 (The source derived subgroup is the same axis).**

$$\forall A \in \operatorname{Type}\left(\right),\; [\operatorname{CommRing}\left(A\right)] \operatorname{sourceDerived}\left(\operatorname{HeisenbergGroup}\left(A\right)\right) = \operatorname{zAxis}\left(A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Heisenberg/CommutingGraph.sourceDerived_axis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* V. Arvind, Peter J. Cameron, Xuanlong Ma and Natalia V. Maslova (2023). *Aspects of the commuting graph*. DOI: [10.48550/arXiv.2305.07301](https://doi.org/10.48550/arXiv.2305.07301). URL: <https://arxiv.org/abs/2305.07301v5>.

*Commentary.*

For arbitrary groups sourceCommutator(x,y) is the native commutator of x inverse and y inverse. Inversion of both generators is bijective, so the two generating sets and their subgroup closures agree. Applying the generic Heisenberg derived-axis theorem gives the displayed source-convention equality. The proof does not assert that the two commutator words are definitionally equal on the original pair.

liftGraphIso accepts an actual bijection of the two-coordinate bases preserving equality of cross products and a bijection of the coefficient carriers. Their product transports all triples bijectively. Equality of cross products is equivalent to commutation of triples. Bijectivity separately preserves inequality of the whole triples. This establishes graph isomorphism without removing centres or requiring bases to be distinct.

## References

- Truth anchor: `D5/S3/FiniteGroups/Heisenberg/CommutingGraph.Isoclinic`
- Truth anchor: `D5/S3/FiniteGroups/Heisenberg/CommutingGraph.commutingGraph`
- Truth anchor: `D5/S3/FiniteGroups/Heisenberg/CommutingGraph.sourceDerived_axis`
- Dependency: [D5/S3/FiniteGroups/Heisenberg/Basic](Basic.md)
