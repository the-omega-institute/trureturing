# Central Orbits of Successful Steiner Switches

## Abstract

Central translations partition the successful starts of each point-deleted Steiner switch.

**Theorem 1.1 (The centre divides the number of successful starts at each pivot).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerSwitchOrbit.successful_starts_dvd_center`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SteinerSwitchOrbit.successful_starts_dvd_center` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Falcone, Ágota Figula, Mario Galici (2025). *Extensions of Steiner Triple Systems*. DOI: [10.1002/jcd.21964](https://doi.org/10.1002/jcd.21964). URL: <https://arxiv.org/abs/2406.12796>.

*Commentary.*

Take a finite complete Steiner triple system and fix a deleted point and a retained pivot. With the matching of uncovered pairs in the retained packing, the number of successful starting labels is divisible by the cardinality of the Steiner loop centre.

Multiplication by a central element commutes with both matching translations. It carries each alternating component to a component of the same size, so it preserves the full-carrier vertices in components of size at least six.

These vertices split into orbits under the central translations. Cancellation gives each orbit exactly as many vertices as there are central elements. The existing image characterization equates their cardinality with that of the successful retained labels. The zero count is included.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerSwitchOrbit.successful_starts_dvd_center`
- Dependency: [D5/S3/Combinatorics/Matroids/SteinerSwitchCentre](SteinerSwitchCentre.md)
