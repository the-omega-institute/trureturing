# Layer Codes 1024 to 2047

## Abstract

An interval of base-three layer codes satisfies the exact support score bound.

**Theorem 1.1 (Exact layer-code interval).**

$$\forall code \in \mathrm{Nat},\; \left(1024 \le code \land code < 2048\right) \Rightarrow \operatorname{exactRow}\left(\mathrm{positions8}, code\right) = \mathrm{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCover8G1.covers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

For positions8, every code from 1024 through 2047 passes exactRow. The exactChunk checks cover this interval; a decoded set of ten vertices has directScore at most twice the support length plus two.

## References

- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCover8G1.covers`
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact](ZeroForcingThreeGapExact.md)
