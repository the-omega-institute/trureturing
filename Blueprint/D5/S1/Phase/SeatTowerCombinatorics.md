# Seat-Tower Combinatorics

This module works with labeled finite indices, independent bounded exponent choices, and Boolean stationings. It does not identify arithmetic orbits with stationings, derive a selector from Jacobi data, or supply any finite orbit certificate. No finite observation, measured exponent, density, or asymptotic law is closed by these theorems.

## Theorem: Reversal swaps parity in an even cycle

Provenance: `repo-derived`

Statement: `D5/S1/Phase/SeatTowerCombinatorics.reversal_swaps_parity` `✓ std3`

For an index inside a cycle of length twice a half-length, the reversed index has the opposite parity. This is an index calculation, not the narrative identity between a reversed canonical word and a rotation.

## Theorem: A parity-matching rotation has odd offset

Provenance: `repo-derived`

Statement: `D5/S1/Phase/SeatTowerCombinatorics.matching_rotation_offset_is_odd` `✓ std3`

If a rotated index is assumed to have the same parity as the reversed index, the rotation offset is odd. The premise connecting an actual periodic word to such a rotation remains explicit and unproved.

## Theorem: Half of the offsets in an even cycle are even

Provenance: `repo-derived`

Statement: `D5/S1/Phase/SeatTowerCombinatorics.even_offset_skeleton_count` `✓ std3`

Doubling gives an explicit equivalence from a half-length index type to the even offsets in the full cycle. The resulting count does not identify offsets with arithmetic orbit classes.

## Theorem: Full exponent choices multiply

Provenance: `repo-derived`

Statement: `D5/S1/Phase/SeatTowerCombinatorics.full_exponent_stationing_count` `✓ std3`

For labeled factors with independent exponent bounds, the number of bounded allocations is the product of the local capacities. No orbit-to-allocation map or bijection is supplied.

## Theorem: Each Boolean mirror pair has a unique normalized member

Provenance: `repo-derived`

Statement: `D5/S1/Phase/SeatTowerCombinatorics.mirror_normalization_is_unique` `✓ std3`

Pointwise Boolean complement exchanges the two labeled sides. Choosing the member whose distinguished coordinate is false gives a unique representative among a stationing and its mirror.

## Theorem: Mirror representatives have power-of-two cardinality

Provenance: `repo-derived`

Statement: `D5/S1/Phase/SeatTowerCombinatorics.mirror_representative_count` `✓ std3`

After fixing the distinguished coordinate, all remaining Boolean coordinates are free, giving exactly two to the free-count representatives. This finite model implies no measured density or asymptotic exponent.
