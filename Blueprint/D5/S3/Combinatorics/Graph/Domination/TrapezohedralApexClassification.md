# Classification by an apex and an opposite label

## Abstract

Every connected minimal dominating subset has exactly one apex and one selected opposite rim label.

All statements concern the original graph on alpha, beta, a(i), b(i), and actual selected vertex subsets. Closed domination and minimality among all proper subsets are unchanged. If both apices are selected, minimality forces the disconnected apex pair. If neither is selected, domination of each apex supplies selected labels of both types. A unique selected label of either type would force all labels of the other type into two neighbors, contradicting n>=3. Closed-private witnesses then force each selected b-vertex to have at most one selected a-neighbor. Connectivity propagates the same a-label along every selected walk, contradicting the existence of two selected a-labels. This avoids any finite-size extrapolation.

**Theorem 1.1 (Exactly one apex).**

$$\forall (n : \mathbb{N}), (3 \le n) \Rightarrow (\forall (S : \operatorname{Set}\left(\operatorname{Vertex}\left(n\right)\right)), (\operatorname{Admissible}\left(S\right)) \Rightarrow (((\operatorname{alpha}\left(\right) \in S) \land (\neg \operatorname{beta}\left(\right) \in S)) \lor ((\operatorname{beta}\left(\right) \in S) \land (\neg \operatorname{alpha}\left(\right) \in S))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TrapezohedralApexClassification.exactly_one_apex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n>=3 and every admissible original subset S, exactly one of alpha and beta belongs to S.

**Theorem 1.2 (The alpha branch).**

$$\forall (n : \mathbb{N}), \forall (S : \operatorname{Set}\left(\operatorname{Vertex}\left(n\right)\right)), (\operatorname{Admissible}\left(S\right)) \Rightarrow ((\operatorname{alpha}\left(\right) \in S) \Rightarrow ((\neg \operatorname{beta}\left(\right) \in S) \Rightarrow (\exists (j : \operatorname{Fin}\left(n\right)), (\operatorname{b}\left(j\right) \in S) \land (\forall (k : \operatorname{Fin}\left(n\right)), (\operatorname{b}\left(k\right) \in S) \Rightarrow (k = j)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TrapezohedralApexClassification.alpha_unique_opposite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If alpha belongs to S and beta does not, exactly one b-label is selected. Connectivity prevents a selected b-vertex from using itself privately; alpha prevents either neighboring a-label from witnessing it privately. Its private witness is therefore beta, which forces uniqueness.

**Theorem 1.3 (Read and reconstruct).**

$$\forall (n : \mathbb{N}), \forall (S : \operatorname{Set}\left(\operatorname{Vertex}\left(n\right)\right)), (\operatorname{Admissible}\left(S\right)) \Rightarrow ((\operatorname{alpha}\left(\right) \in S) \Rightarrow ((\neg \operatorname{beta}\left(\right) \in S) \Rightarrow (\exists (j : \operatorname{Fin}\left(n\right)), (S = \operatorname{alphaSet}\left(j, \{i : \operatorname{Fin}\left(n\right) \mid \operatorname{a}\left(i\right) \in S\}\right)) \land (\forall (k : \operatorname{Fin}\left(n\right)), (S = \operatorname{alphaSet}\left(k, \{i : \operatorname{Fin}\left(n\right) \mid \operatorname{a}\left(i\right) \in S\}\right)) \Rightarrow (k = j)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TrapezohedralApexClassification.alpha_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the alpha branch the unique selected b-label j and the membership of the selected a-labels reconstruct the entire original subset. Different j cannot reconstruct the same subset. No quotient by graph symmetries is taken.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralApexClassification.alpha_reconstruction`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralApexClassification.alpha_unique_opposite`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralApexClassification.exactly_one_apex`
- Dependency: [D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination](TrapezohedralMinimalDomination.md)
