# Two-Thirds Bound for Dominating-Set Averages

## Abstract

The inequality is Theorem 2.9 of Iain Beaton and Ben Cameron, A Tight Upper Bound on the Average Order of Dominating Sets of a Graph, arXiv:2208.10475. Stem blocks are grouped by their vertex sets, so a two-vertex component gives one block.

**Definition 1.1 (Active stem blocks).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.activeBlocks`

*Formalization.* `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.activeBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A leaf-stem block is active for a selected set when at least one vertex in the block is omitted.

**Definition 1.2 (Residual vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.residual`

*Formalization.* `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.residual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The residual vertices lie outside the union of the active stem blocks.

**Definition 1.3 (Vertices outside all stem blocks).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.core`

*Formalization.* `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.core` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The core consists of vertices belonging to no leaf-stem block.

**Theorem 1.4 (Private neighbours remain residual).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.privateNeighbor_residual`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.privateNeighbor_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A private outside neighbour of a selected residual vertex also lies in the residual set.

**Theorem 1.5 (Residual private-neighbour estimate).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.externallyCritical_residual_card_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.externallyCritical_residual_card_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The number of externally critical residual vertices is bounded by the number of residual private outside neighbours.

**Theorem 1.6 (Self-critical residual vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.selfCritical_inter_residual`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.selfCritical_inter_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a dominating set, the self-critical residual vertices are precisely the self-critical vertices in the core.

**Theorem 1.7 (Residual incidence estimate).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.residual_total_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.residual_total_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In an isolate-free graph, the total number of residual critical incidences is at most the total number of residual omitted incidences.

**Theorem 1.8 (Active-block incidence estimate).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.active_block_total_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.active_block_total_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing over all active stem blocks and all dominating sets gives no more critical incidences than omitted incidences.

**Theorem 1.9 (Global incidence estimate).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.critical_total_le_omitted_total`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.critical_total_le_omitted_total` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The total number of critical incidences over all dominating sets is at most the total number of omitted incidences in an isolate-free finite graph.

**Theorem 1.10 (Beaton–Cameron inequality).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.avd_le_two_thirds`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.avd_le_two_thirds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite graph G without isolated vertices, avd(G) is at most 2|V(G)|/3. The empty graph is included and has average zero.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.activeBlocks`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.active_block_total_le`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.avd_le_two_thirds`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.core`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.critical_total_le_omitted_total`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.externallyCritical_residual_card_le`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.privateNeighbor_residual`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.residual`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.residual_total_le`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBound.selfCritical_inter_residual`
- Dependency: [D5/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem](DominatingSetAverageBoundNonstem.md)
- Dependency: [D5/S3/Combinatorics/Graph/DominatingSetAverageBoundStem](DominatingSetAverageBoundStem.md)
