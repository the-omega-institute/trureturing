# Neighbour Replacement for Self-Critical Vertices

## Abstract

The neighbour-replacement argument is the strict critical-incidence comparison in the proof of Theorem 2.9 of Iain Beaton and Ben Cameron, A Tight Upper Bound on the Average Order of Dominating Sets of a Graph, arXiv:2208.10475.

**Definition 1.1 (Self-critical vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem.selfCritical`

*Formalization.* `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem.selfCritical` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A self-critical vertex is critical and has no private neighbour outside the selected set.

**Theorem 1.2 (Domination after deletion).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem.selfCritical_erase_dominates_other`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem.selfCritical_erase_dominates_other` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Deleting a self-critical vertex leaves every other vertex dominated.

**Theorem 1.3 (No selected neighbour).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem.selfCritical_no_selected_neighbor`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem.selfCritical_no_selected_neighbor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A self-critical vertex has no neighbour in the dominating set.

**Theorem 1.4 (Neighbour replacement).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem.selfCritical_neighbor_replacement`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem.selfCritical_neighbor_replacement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A self-critical vertex can be deleted and replaced by any nonempty collection of its neighbours without destroying domination.

**Theorem 1.5 (Injective replacement).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem.selfCritical_neighbor_replacement_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem.selfCritical_neighbor_replacement_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a fixed vertex and a fixed set of its neighbours, replacing a self-critical vertex by that set is injective among dominating sets.

**Theorem 1.6 (Non-strict incidence comparison).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem.selfCriticalSets_card_le_multiNeighborSets`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem.selfCriticalSets_card_le_multiNeighborSets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a vertex of degree at least two, the number of self-critical dominating sets is at most the number omitting the vertex while selecting at least two neighbours.

**Definition 1.7 (A dominating set outside the replacement image).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem.neighborWitness`

*Formalization.* `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem.neighborWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Select every neighbour of the fixed vertex and every other vertex outside the closed neighbourhoods of these neighbours.

**Theorem 1.8 (Strict incidence comparison).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem.selfCriticalSets_card_lt_multiNeighborSets`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem.selfCriticalSets_card_lt_multiNeighborSets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a vertex of degree at least two, the number of self-critical dominating sets is strictly smaller than the number omitting the vertex while selecting at least two neighbours. The neighbour witness is outside the image of replacement.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem.neighborWitness`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem.selfCritical`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem.selfCriticalSets_card_le_multiNeighborSets`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem.selfCriticalSets_card_lt_multiNeighborSets`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem.selfCritical_erase_dominates_other`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem.selfCritical_neighbor_replacement`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem.selfCritical_neighbor_replacement_injective`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem.selfCritical_no_selected_neighbor`
- Dependency: [D5/S3/Combinatorics/Graph/DominatingSetAverageBoundCounting](DominatingSetAverageBoundCounting.md)
