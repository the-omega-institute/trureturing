# Source Shape Extraction

## Abstract

Endpoint and exterior fixed-point data force the first-orientation shape in every singleton word.

Fix the first orientation with 1<=m<i<=j<M<=n. The permutation product applies the rightmost generator first. A singleton word here is an actual reduced consecutive word for sigma. EndpointExteriorFixedSource consists only of these order bounds, the three endpoint equations, and fixed points outside [m,M+1]. It assumes neither a nonoscillating word nor separate nonfixed endpoint clauses.

**Definition 1.1 (Endpoint and exterior fixed-point hypothesis).**

$$\operatorname {EndpointExteriorFixedSource}\left(n, m, M, i, j, sigma\right) \iff 1 \le m < i \le j < M \le n \land \operatorname {sigma}\left(\operatorname {position}\left(n, M + 1\right)\right) = \operatorname {position}\left(n, m\right) \land \operatorname {sigma}\left(\operatorname {position}\left(n, m\right)\right) = \operatorname {position}\left(n, j + 1\right) \land \operatorname {sigma}\left(\operatorname {position}\left(n, i\right)\right) = \operatorname {position}\left(n, M + 1\right) \land \forall k \in \operatorname {Fin}\left(n + 1\right) , (\operatorname {val}\left(k\right) + 1 < m \lor M + 1 < \operatorname {val}\left(k\right) + 1) \implies \operatorname {sigma}\left(k\right) = k$$

*Formalization.* `D5/S1/Words/Permutations/MamedeShapeExtraction.endpointExteriorFixedSource` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ricardo Mamede, Jose Luis Santos, Diogo Soares (2026). *Maximum number of one-element commutation classes of a permutation*. DOI: [10.48550/arXiv.2601.09395](https://doi.org/10.48550/arXiv.2601.09395).

*Commentary.*

The exact Lean definition has no oscillation or nonfixed endpoint clause; the three endpoint equations and outside fixed points are its only permutation conditions.

**Theorem 1.2 (Three forced runs and generator support).**

$$\operatorname {EndpointExteriorFixedSource}\left(n, m, M, i, j, sigma\right) \land \operatorname {Singleton}\left(n, sigma, a\right) \implies \operatorname {FirstDescent}\left(a, j, m\right) \land \operatorname {CentralAscent}\left(a, m, M\right) \land \operatorname {LastDescent}\left(a, M, i\right) \land \operatorname {GeneratorSupport}\left(a, m, M\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/MamedeShapeExtraction.source_forced_runs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ricardo Mamede, Jose Luis Santos, Diogo Soares (2026). *Maximum number of one-element commutation classes of a permutation*. DOI: [10.48550/arXiv.2601.09395](https://doi.org/10.48550/arXiv.2601.09395).

*Commentary.*

FirstDescent means a=p++descending(j,m)++q, all letters of p are below j and all letters of q exceed m. CentralAscent means a=p++ascending(m,M)++q, all letters of p exceed m and all letters of q are below M. LastDescent means a=p++descending(M,i)++q, all letters of p are below M and all letters of q exceed i. Each decomposition has its own p and q. GeneratorSupport means every letter of a lies in [m,M]. The three decompositions are initially separate; the next theorem aligns them. This endpoint-based strengthening is repository-derived; the cited paper's Proposition 3.3 and Lemma 3.6 do not assert it under these weaker premises.

**Theorem 1.3 (Every source singleton has the first orientation).**

$$\operatorname {EndpointExteriorFixedSource}\left(n, m, M, i, j, sigma\right) \land \operatorname {Singleton}\left(n, sigma, a\right) \implies \exists p , \exists q , \operatorname {SourceShape}\left(m, M, i, j, a, p, q\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/MamedeShapeExtraction.source_shape_for_every_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ricardo Mamede, Jose Luis Santos, Diogo Soares (2026). *Maximum number of one-element commutation classes of a permutation*. DOI: [10.48550/arXiv.2601.09395](https://doi.org/10.48550/arXiv.2601.09395).

*Commentary.*

The unique shared occurrences of m and M align the three forced runs into one Full(m,M,i,j). The first prefix lies strictly in (m,j), and the final suffix lies strictly in (i,M). This endpoint-based strengthening is proved in Lean for each actual singleton word. The cited paper derives endpoint identities from a nonoscillating word; this theorem starts from explicit endpoint identities. This does not resolve Conjecture 5.1.

## References

- Truth anchor: `D5/S1/Words/Permutations/MamedeShapeExtraction.endpointExteriorFixedSource`
- Truth anchor: `D5/S1/Words/Permutations/MamedeShapeExtraction.source_forced_runs`
- Truth anchor: `D5/S1/Words/Permutations/MamedeShapeExtraction.source_shape_for_every_singleton`
- Dependency: [D5/S1/Words/Permutations/MamedeCrossing](MamedeCrossing.md)
