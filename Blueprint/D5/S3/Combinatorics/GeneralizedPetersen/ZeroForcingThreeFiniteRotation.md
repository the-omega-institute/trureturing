# Rotation Preserves Adjacency

## Abstract

Column rotations preserve all edges of P(13,3).

**Theorem 1.1 (Adjacency under column rotation).**

$$\forall r \in \operatorname{Fin}\left(13\right),\; \forall v \in \mathrm{V13},\; \forall w \in \mathrm{V13},\; \operatorname{Adj}\left(\operatorname{gp}\left(13, 3\right), \operatorname{rotate13}\left(r, v\right), \operatorname{rotate13}\left(r, w\right)\right) \Leftrightarrow \operatorname{Adj}\left(\operatorname{gp}\left(13, 3\right), v, w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteRotation.rotate13_adj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Subtracting the same column index preserves outer edges, inner step-three edges, and spokes.

## References

- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteRotation.rotate13_adj`
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ParityRefutation](ParityRefutation.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore](ZeroForcingThreeFiniteCore.md)
