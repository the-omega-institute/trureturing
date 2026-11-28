# Two categorical pieces for the seven-triangle face-poset product

## Abstract

Two categorical pieces for the seven-triangle face-poset product

**Theorem 1.1 (Two categorical lower sets after two ordinary subdivisions).**

Lean statement: `D5/S3/Topology/StableCategory/ProductStableCover.product_two_after_two_subdivisions`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StableCategory/ProductStableCover.product_two_after_two_subdivisions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

Deleting the three up-beat boundary edges in each factor leaves a 484-point product core. A finite search supplies a partition and two coordinate trajectories for each core point. The Lean kernel checks that each row is monotone within its colour, starts at the inclusion, ends at a constant, and changes by six alternating pointwise comparisons. Pulling back along the beat retraction and applying the ordinary subdivision cover construction gives the two lower sets.

## References

- Truth anchor: `D5/S3/Topology/StableCategory/ProductStableCover.product_two_after_two_subdivisions`
- Dependency: [D5/S3/Topology/StableCategory/ProductRigidCores](ProductRigidCores.md)
- Dependency: [D5/S3/Topology/SubdivisionCategoricalCover](../SubdivisionCategoricalCover.md)
