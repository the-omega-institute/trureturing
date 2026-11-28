# Moving the anchor across a mixed cone attachment

## Abstract

Moving the anchor across a mixed cone attachment

**Theorem 1.1 (A deformation inside the actual cone base gives an exact categorical two-cover).**

Lean statement: `D5/S3/Topology/StableCategory/MovingAnchorMixedCone.moving_anchor_exact_two_cover_of_adjoined_maximum`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StableCategory/MovingAnchorMixedCone.moving_anchor_exact_two_cover_of_adjoined_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

The first retained region trims coned faces meeting its trace vertices. On the second retained region, an order-map fence keeps each wholly exclusive base face inside the actual cone base. Cone each image around the fixed apex, then insert a terminal anchor spanning the moved faces and delete the apex. Two further ordinary subdivisions give categorical lower sets with the two prescribed old intersections. The homotopy on the second piece may move its old points.

## References

- Truth anchor: `D5/S3/Topology/StableCategory/MovingAnchorMixedCone.moving_anchor_exact_two_cover_of_adjoined_maximum`
- Dependency: [D5/S3/Topology/StableCategory/InheritedDepthConeAttachment](InheritedDepthConeAttachment.md)
