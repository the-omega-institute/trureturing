# Recovering endpoint selections

## Abstract

Endpoint splitting inverts the selected odd-block construction.

The bijection is source Proposition 3.3(i)-(ii). The exact-range statement records the additional formal recovery criterion used for part (iii).

**Theorem 1.1 (Bijection at every quotient size at least three).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEndpointRecovery.crownOddBlockMerge_bijective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEndpointRecovery.crownOddBlockMerge_bijective` (`✓ std3`). ∎

*Citation.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

For n at least two and k at least three, the actual odd-block merge map is bijective between selections producing k augmented blocks and connected compatible partitions with k blocks. Endpoint splitting provides the inverse and proves oddness of the recovered selected components.

**Theorem 1.2 (The exact range before exceptional cases).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEndpointRecovery.twoSidedMergeCCP_range_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEndpointRecovery.twoSidedMergeCCP_range_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

For n at least two, an augmented connected compatible partition comes from odd-block merging exactly when its endpoints are separate and neither endpoint is related to every original vertex. This identifies the two exceptional two-block partitions.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEndpointRecovery.crownOddBlockMerge_bijective`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEndpointRecovery.twoSidedMergeCCP_range_iff`
- Dependency: [D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEndpointMergers](CrownOrderPolytopeEndpointMergers.md)
