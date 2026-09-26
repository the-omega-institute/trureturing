# Layer Codes 3072 to 4095

## Abstract

An interval of base-three layer codes satisfies the exact support score bound.

**Theorem 1.1 (Exact layer-code interval).**

$$\forall code \in \mathrm{Nat},\; \left(3072 \le code \land code < 4096\right) \Rightarrow \operatorname{exactRow}\left(\mathrm{positions8}, code\right) = \mathrm{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCover8G3.covers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

For positions8, every code from 3072 through 4095 passes exactRow. The exactChunk checks cover this interval; a decoded set of ten vertices has directScore at most twice the support length plus two.

## References

- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCover8G3.covers`
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact](ZeroForcingThreeGapExact.md)
