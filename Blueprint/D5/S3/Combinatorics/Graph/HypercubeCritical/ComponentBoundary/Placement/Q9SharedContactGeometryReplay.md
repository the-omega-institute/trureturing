# Replay the three shared-contact refutations

## Abstract

Kernel-checked refutations exclude all three normalized shared distance-three contacts.

**Theorem 1.1 (Distance-three contacts have disjoint occupied directions).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactGeometryReplay.no_shared_distance_three`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactGeometryReplay.no_shared_distance_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Normalize the shared contact using its overlap size. For every input clause in the corresponding refutation, Lean checks that the local rules imply the exact clause appearing in the formula. Mathlib's LRAT proof replays the derivation of the empty clause under that valuation. The three certificates cover overlap sizes one, two and three.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactGeometryReplay.no_shared_distance_three`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactCNF](Q9SharedContactCNF.md)
