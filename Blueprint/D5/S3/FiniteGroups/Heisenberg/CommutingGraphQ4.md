# Non-isoclinic pairs at every prime-sixth order

## Abstract

For every prime p, two groups of order p to the sixth have isomorphic full commuting graphs and are not isoclinic.

**Definition 1.1 (The exact quantified event).**

$$ExactEvent = \left(\forall p \in \mathbb{N},\; (\operatorname{NatPrime}\left(p\right)) \Rightarrow (\exists G \in \operatorname{FiniteGroup}\left(\right),\; \exists H \in \operatorname{FiniteGroup}\left(\right),\; (\operatorname{NatCard}\left(\operatorname{Carrier}\left(G\right)\right) = p^{6}) \land ((\operatorname{NatCard}\left(\operatorname{Carrier}\left(H\right)\right) = p^{6}) \land ((\operatorname{Nonempty}\left(\operatorname{GraphIso}\left(\operatorname{commutingGraph}\left(\operatorname{Carrier}\left(G\right)\right), \operatorname{commutingGraph}\left(\operatorname{Carrier}\left(H\right)\right)\right)\right)) \land (\neg (\operatorname{Isoclinic}\left(\operatorname{Carrier}\left(G\right), \operatorname{Carrier}\left(H\right)\right))))))\right)$$

*Formalization.* `D5/S3/FiniteGroups/Heisenberg/CommutingGraphQ4.ExactEvent` (`✓ std3`).

*Citation.* V. Arvind, Peter J. Cameron, Xuanlong Ma and Natalia V. Maslova (2023). *Aspects of the commuting graph*. DOI: [10.48550/arXiv.2305.07301](https://doi.org/10.48550/arXiv.2305.07301). URL: <https://arxiv.org/abs/2305.07301v5>.

*Commentary.*

Section 9, Q4, page 40 asks: What can be said about pairs of groups with isomorphic commuting graphs? Do non-isoclinic examples exist for all orders p^6 with p prime? Only the second sentence is the assertion here. FiniteGroup is the existing bundle of a carrier type, an actual Group structure and finiteness. The graph uses every element as a vertex, with adjacency exactly unequal whole elements whose products commute. Isoclinic means compatible group isomorphisms on the central quotients and source derived subgroups, intertwining x inverse times y inverse times x times y for all representatives.

**Theorem 1.2 (The derived groups obstruct isoclinism).**

$$\forall p \in \mathbb{N},\; (\operatorname{NatPrime}\left(p\right)) \Rightarrow (\neg (\operatorname{Isoclinic}\left(\operatorname{Carrier}\left(\operatorname{squareGroup}\left(p\right)\right), \operatorname{Carrier}\left(\operatorname{dualGroup}\left(p\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Heisenberg/CommutingGraphQ4.not_isoclinic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* V. Arvind, Peter J. Cameron, Xuanlong Ma and Natalia V. Maslova (2023). *Aspects of the commuting graph*. DOI: [10.48550/arXiv.2305.07301](https://doi.org/10.48550/arXiv.2305.07301). URL: <https://arxiv.org/abs/2305.07301v5>.

*Commentary.*

Take R=ZMod(p*p) and S=DualNumber(ZMod p). The groups squareGroup and dualGroup are the Heisenberg triples over R and S. Their source derived subgroups are exactly the central z-axes. In R the element with central coordinate one has nonidentity p-th power because p is nonzero modulo p*p. Every element of the S axis is killed by the p-th power. A group isomorphism preserves powers, so no derived-group isomorphism exists. This already prevents isoclinism and needs no classification of the full centre.

**Theorem 1.3 (An affirmative answer for every prime).**

$$\forall p \in \mathbb{N},\; (\operatorname{NatPrime}\left(p\right)) \Rightarrow (\exists G \in \operatorname{FiniteGroup}\left(\right),\; \exists H \in \operatorname{FiniteGroup}\left(\right),\; (\operatorname{NatCard}\left(\operatorname{Carrier}\left(G\right)\right) = p^{6}) \land ((\operatorname{NatCard}\left(\operatorname{Carrier}\left(H\right)\right) = p^{6}) \land ((\operatorname{Nonempty}\left(\operatorname{GraphIso}\left(\operatorname{commutingGraph}\left(\operatorname{Carrier}\left(G\right)\right), \operatorname{commutingGraph}\left(\operatorname{Carrier}\left(H\right)\right)\right)\right)) \land (\neg (\operatorname{Isoclinic}\left(\operatorname{Carrier}\left(G\right), \operatorname{Carrier}\left(H\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Heisenberg/CommutingGraphQ4.result` (`✓ std3`). ∎

*Resolves.* `Problems/arvind-2023-commuting-graph-q4` (proved) by `D5/S3/FiniteGroups/Heisenberg/CommutingGraphQ4.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"arvind-2023-commuting-graph-q4","declaration_gid":"D5/S3/FiniteGroups/Heisenberg/CommutingGraphQ4.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* V. Arvind, Peter J. Cameron, Xuanlong Ma and Natalia V. Maslova (2023). *Aspects of the commuting graph*. DOI: [10.48550/arXiv.2305.07301](https://doi.org/10.48550/arXiv.2305.07301). URL: <https://arxiv.org/abs/2305.07301v5>.

*Commentary.*

Use the same two coefficient rings for each prime. Each ring has p*p elements, hence each triple group has order p^6. The prime-two case is included throughout; there is no division by two. The residue-chart construction supplies a bijection of the two-coordinate bases preserving equality of cross products for every pair. A coefficient bijection supplies the third coordinate. Their product is a bijection on whole triples, so distinctness is preserved even for equal bases with different z coordinates. Equality xY=Xy is exactly group commutation, yielding an isomorphism of the full simple commuting graphs.

The three disjoint base charts are (u,ut), (us,u) with u a unit and s in the maximal ideal, and pairs in that ideal. Within a primitive chart, equality of fine slopes decides incidence. The two primitive charts are never incident to each other. Between a finite-slope chart and an ideal vector (j(a),j(b)), incidence is b=res(t)*a. Between the other primitive chart and an ideal vector it is a=0. Every two ideal vectors are incident. The zero vector therefore remains incident to every vector. This common relation retains the fine slope and its residue rather than identifying them.

The generic group, power, cardinality and derived-axis APIs are an attributed compatible Tau Ceti port. They do not supply the graph-incidence bijection. The source already reports examples at primes two, three and five. The theorem covers every natural prime and does not claim a classification, minimal order, worldwide priority or a complete answer to the first sentence of Q4. The bounded source and supplier search does not establish exhaustive later-literature coverage.

## References

- Truth anchor: `D5/S3/FiniteGroups/Heisenberg/CommutingGraphQ4.ExactEvent`
- Truth anchor: `D5/S3/FiniteGroups/Heisenberg/CommutingGraphQ4.not_isoclinic`
- Truth anchor: `D5/S3/FiniteGroups/Heisenberg/CommutingGraphQ4.result`
- Dependency: [D5/S3/FiniteGroups/Heisenberg/CommutingGraph](CommutingGraph.md)
- Dependency: [D5/S3/FiniteGroups/Heisenberg/PrimeSquareCoordinates](PrimeSquareCoordinates.md)
- Dependency: [D5/S3/FiniteGroups/SubgroupConjugacyRatio](../SubgroupConjugacyRatio.md)
