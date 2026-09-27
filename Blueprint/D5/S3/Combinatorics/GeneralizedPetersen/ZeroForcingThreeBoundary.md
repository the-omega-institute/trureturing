# External Boundary in P(n,3)

## Abstract

The external boundary consists of unselected vertices adjacent to the selected set.

**Definition 1.1 (External vertex boundary).**

$$\forall n \in \mathrm{Nat},\; \forall X \in \operatorname{Finset}\left(\mathrm{Bool}\times \operatorname{Fin}\left(n\right)\right),\; \operatorname{externalBoundary}\left(n, X\right) = \{ v \in \mathrm{Bool}\times \operatorname{Fin}\left(n\right)| \left(\neg v \in X\right) \land \left(\exists u \in \mathrm{Bool}\times \operatorname{Fin}\left(n\right),\; u \in X \land \operatorname{Adj}\left(\operatorname{gp}\left(n, 3\right), u, v\right)\right)\} $$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeBoundary.externalBoundary` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

A vertex is in the external boundary when it lies outside X and has a neighbor in X.

## References

- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeBoundary.externalBoundary`
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ParityRefutation](ParityRefutation.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeShiftCore](ZeroForcingThreeShiftCore.md)
