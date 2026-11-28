# Exact categorical transport across a mixed simplex attachment

## Abstract

Exact categorical transport across a mixed simplex attachment

**Theorem 1.1 (Two regions from disjoint vertex blocks).**

Lean statement: `D5/S3/Topology/StableCategory/MixedSimplexChart.mixed_block_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StableCategory/MixedSimplexChart.mixed_block_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

A forbidden image requires a nonempty face in its own vertex block. Disjoint blocks give incomparable faces, which cannot both occur in the same chain. Their two pullbacks therefore cover the second ordinary barycentric subdivision.

**Theorem 1.2 (Transport with exact old intersections).**

Lean statement: `D5/S3/Topology/StableCategory/MixedSimplexAttachment.mixed_exact_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StableCategory/MixedSimplexAttachment.mixed_exact_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

When the two old categorical pieces meet an attaching simplex in the prescribed horns and satisfy the exterior incidence conditions, the two full regions at depth two contract in the common ambient. One further ordinary subdivision gives a two-piece cover with the prescribed old intersections exactly.

## References

- Truth anchor: `D5/S3/Topology/StableCategory/MixedSimplexAttachment.mixed_exact_transport`
- Truth anchor: `D5/S3/Topology/StableCategory/MixedSimplexChart.mixed_block_cover`
- Dependency: [D5/S3/Topology/StableCategory/ExactCategoricalExtension](ExactCategoricalExtension.md)
