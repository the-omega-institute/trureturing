# Allocate disjoint exponent positions to classes of sizes one through four

## Abstract

Allocate disjoint exponent positions to classes of sizes one through four.

**Theorem 1.1 (card_classPositions).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Allocation.card_classPositions`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Allocation.card_classPositions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dingying Ma (2026). *On Distinct Powers in Finite Groups*. DOI: [10.48550/arXiv.2611.13582](https://doi.org/10.48550/arXiv.2611.13582). URL: <https://arxiv.org/abs/2611.13582v1>.

*Commentary.*

Sum the number of positions over each populated class-size bucket.

**Theorem 1.2 (slot_lt).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Allocation.slot_lt`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Allocation.slot_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dingying Ma (2026). *On Distinct Powers in Finite Groups*. DOI: [10.48550/arXiv.2611.13582](https://doi.org/10.48550/arXiv.2611.13582). URL: <https://arxiv.org/abs/2611.13582v1>.

*Commentary.*

Each allotted position is below n when the class counts account for n elements.

**Theorem 1.3 (slot_injective).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Allocation.slot_injective`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Allocation.slot_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dingying Ma (2026). *On Distinct Powers in Finite Groups*. DOI: [10.48550/arXiv.2611.13582](https://doi.org/10.48550/arXiv.2611.13582). URL: <https://arxiv.org/abs/2611.13582v1>.

*Commentary.*

The two endpoint ranges and the disjoint middle intervals make the assignment injective.

**Theorem 1.4 (pair_slots).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Allocation.pair_slots`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Allocation.pair_slots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dingying Ma (2026). *On Distinct Powers in Finite Groups*. DOI: [10.48550/arXiv.2611.13582](https://doi.org/10.48550/arXiv.2611.13582). URL: <https://arxiv.org/abs/2611.13582v1>.

*Commentary.*

Each pair receives distinct complementary exponents whose sum is n + 1.

**Theorem 1.5 (triple_slots).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Allocation.triple_slots`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Allocation.triple_slots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dingying Ma (2026). *On Distinct Powers in Finite Groups*. DOI: [10.48550/arXiv.2611.13582](https://doi.org/10.48550/arXiv.2611.13582). URL: <https://arxiv.org/abs/2611.13582v1>.

*Commentary.*

Each triple gets three consecutive exponents after the first endpoint range.

**Theorem 1.6 (four_slots).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Allocation.four_slots`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Allocation.four_slots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dingying Ma (2026). *On Distinct Powers in Finite Groups*. DOI: [10.48550/arXiv.2611.13582](https://doi.org/10.48550/arXiv.2611.13582). URL: <https://arxiv.org/abs/2611.13582v1>.

*Commentary.*

Each quadruple gets four consecutive exponents after the triples.

## References

- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Allocation.card_classPositions`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Allocation.four_slots`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Allocation.pair_slots`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Allocation.slot_injective`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Allocation.slot_lt`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Allocation.triple_slots`
