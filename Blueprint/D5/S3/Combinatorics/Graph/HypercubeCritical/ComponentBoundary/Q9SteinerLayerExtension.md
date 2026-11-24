# Steiner reconstruction and the sharp extension bound

## Abstract

The sharp extension bound for Steiner supports in Q9

**Theorem 1.1 (The missing triples form a Steiner triple system).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SteinerLayerExtension.missing_triples_steiner`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SteinerLayerExtension.missing_triples_steiner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A cubic support of size 144 in layers 3 and 4 has 72 vertices in each layer. Each selected triple has three of its six upper neighbors outside the support. This yields 216 incidences with the 54 omitted four-sets, so every omitted four-set contains four selected triples.

Every selected four-set contains exactly one missing triple by cubicity. Two missing triples can never share a pair because their union would then be a four-set containing both. The twelve missing triples cover all 36 pairs exactly once.

**Theorem 1.2 (The closed-neighborhood complement consists of six layers).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SteinerLayerExtension.mem_residual_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SteinerLayerExtension.mem_residual_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every pair belongs to six selected triples. Every five-set contains a missing triple because its ten pairs could otherwise be completed only at the four outside points, with each outside point completing a matching of size at most two. Thus the closed neighborhood contains every vertex of layers 2 through 5.

**Theorem 1.3 (A subcubic extension has at most 246 vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SteinerLayerExtension.extension_card_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SteinerLayerExtension.extension_card_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every added vertex lies outside the closed neighborhood, since the original support is already cubic. Let k be the number of retained layer-7 vertices and d the number of omitted layer-6 vertices. Each retained vertex has at least four omitted lower neighbors, while each omitted lower vertex can serve at most three retained upper vertices. Hence 4k ≤ 3d, and d + 36 − k is at least 36.

The separate nine-leaf stars on layers 0 and 1 and on layers 8 and 9 each require another omission. The six residual layers have 140 vertices, so the complete extension has at most 144 + 140 − 38 = 246 vertices. This excludes the Steiner family from the 258-vertex case of the external problem. https://arxiv.org/html/2610.09483v1#Thmproblem2

**Theorem 1.4 (Exactly one extension attains 246 vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SteinerLayerExtension.extension_card_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SteinerLayerExtension.extension_card_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Keeping any layer-7 vertex makes the middle omission bound strict. A star with exactly one omission must lose its center. Thus equality forces the omission of layers 0, 7 and 9 and the retention of layers 1, 6 and 8. These three retained layers have no edges between them, so they attain the bound.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SteinerLayerExtension.extension_card_eq_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SteinerLayerExtension.extension_card_le`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SteinerLayerExtension.mem_residual_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SteinerLayerExtension.missing_triples_steiner`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LevelThreeFourObstruction](Q9LevelThreeFourObstruction.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenSaturation](../SupportedEigenSaturation.md)
