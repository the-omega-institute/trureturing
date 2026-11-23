# Connected colored blocks and literal lower intervals

## Abstract

Connected colored blocks and literal lower intervals.

**Definition 1.1 (MultiweightedBond).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.MultiweightedBond`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/FiniteOrder.MultiweightedBond` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

Each block induces a connected graph and has a weak composition of its size minus one across Fin(r). Every weight outside the partition blocks is zero.

**Theorem 1.2 (ext_weights).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.ext_weights`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/FiniteOrder.ext_weights` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

Two elements with the same partition agree if their weights agree on its blocks in every color.

**Definition 1.3 (childSum).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.childSum`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/FiniteOrder.childSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

For a given vertex set and color, sum the weights of the partition blocks contained in that set.

**Definition 1.4 (Refines).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.Refines`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/FiniteOrder.Refines` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

The partition refines the upper partition and each upper weight dominates the sum of the finer weights in that color.

**Definition 1.5 (singletonZero).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.singletonZero`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/FiniteOrder.singletonZero` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

The bottom consists of singleton blocks with all weights zero.

**Theorem 1.6 (complete_block_connected).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.complete_block_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/FiniteOrder.complete_block_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

Every nonempty block of a partition in the complete graph induces a connected graph.

**Theorem 1.7 (weight_eq_zero_of_card_one).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.weight_eq_zero_of_card_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/FiniteOrder.weight_eq_zero_of_card_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

A singleton block has zero weight in every color.

**Theorem 1.8 (total_weight_eq_rank).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.total_weight_eq_rank`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/FiniteOrder.total_weight_eq_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

Summing the block weights over every color gives the vertex count minus the number of blocks.

**Definition 1.9 (CompleteBond).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.CompleteBond`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/FiniteOrder.CompleteBond` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

The finite colored bond poset of the complete graph on Fin(n).

**Definition 1.10 (psiComplete).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.psiComplete`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/FiniteOrder.psiComplete` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

Sum the integer incidence Möbius coefficients from the singleton bottom, each multiplied by X to the number of vertices minus the number of blocks.

**Definition 1.11 (restrictBlock).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.restrictBlock`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/FiniteOrder.restrictBlock` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

Restrict the finer partition and its weights to an upper block, using the induced graph on its vertex subtype.

**Definition 1.12 (oneBlock).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.oneBlock`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/FiniteOrder.oneBlock` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

The weighted partition of an upper block into itself, with the upper block's original color weights.

**Theorem 1.13 (oneBlock_parts).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.oneBlock_parts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/FiniteOrder.oneBlock_parts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

The one-block partition has just the full vertex set of the block.

**Theorem 1.14 (oneBlock_weight).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.oneBlock_weight`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/FiniteOrder.oneBlock_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

The weight of its full vertex set equals the weight of the corresponding upper block in every color.

**Definition 1.15 (recombineBlocks).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.recombineBlocks`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/FiniteOrder.recombineBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

Glue the block partitions in their disjoint ambient sets and transport each coordinate of their weights back to the original graph.

**Theorem 1.16 (restrictBlock_recombineBlocks).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.restrictBlock_recombineBlocks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/FiniteOrder.restrictBlock_recombineBlocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

Restriction to any upper block recovers that block's input after recombination.

**Theorem 1.17 (recombineBlocks_restrictBlock).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.recombineBlocks_restrictBlock`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/FiniteOrder.recombineBlocks_restrictBlock` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

Recombining all restrictions recovers the original partition and all its weights.

**Definition 1.18 (lowerIntervalOrderIso).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.lowerIntervalOrderIso`

*Formalization.* `D5/S3/Combinatorics/WeightedBond/FiniteOrder.lowerIntervalOrderIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

The lower interval of an upper weighted partition is order-isomorphic to the dependent product of the lower intervals below its one-block restrictions in the induced graphs.

**Theorem 1.19 (mu_bot_iic).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.mu_bot_iic`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/FiniteOrder.mu_bot_iic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

Restricting to a lower interval leaves every Möbius coefficient from the bottom unchanged.

**Theorem 1.20 (mu_bot_orderIso).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.mu_bot_orderIso`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/FiniteOrder.mu_bot_orderIso` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

An order isomorphism of locally finite orders with bottoms preserves the bottom Möbius function.

**Theorem 1.21 (mu_bot_eq_prod_blocks).**

Lean statement: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.mu_bot_eq_prod_blocks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeightedBond/FiniteOrder.mu_bot_eq_prod_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

The Möbius value from bottom to an upper weighted partition is the product of the corresponding bottom-to-one-block values on its blocks.

## References

- Truth anchor: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.CompleteBond`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.MultiweightedBond`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.Refines`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.childSum`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.complete_block_connected`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.ext_weights`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.lowerIntervalOrderIso`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.mu_bot_eq_prod_blocks`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.mu_bot_iic`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.mu_bot_orderIso`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.oneBlock`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.oneBlock_parts`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.oneBlock_weight`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.psiComplete`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.recombineBlocks`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.recombineBlocks_restrictBlock`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.restrictBlock`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.restrictBlock_recombineBlocks`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.singletonZero`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.total_weight_eq_rank`
- Truth anchor: `D5/S3/Combinatorics/WeightedBond/FiniteOrder.weight_eq_zero_of_card_one`
- Dependency: [D5/S0/Certificates/GonzalezDLeonWachsWeightedBondSource](../../../S0/Certificates/GonzalezDLeonWachsWeightedBondSource.md)
