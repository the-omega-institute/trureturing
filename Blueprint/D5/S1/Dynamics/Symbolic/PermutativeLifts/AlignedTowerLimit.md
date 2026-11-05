# Compact aligned tower limits with periodic coordinates

## Abstract

Compact aligned tower limits with periodic coordinates.

**Definition 1.1 (Periodic coordinates).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/AlignedTowerLimit.HasPeriodicCoordinates`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/AlignedTowerLimit.HasPeriodicCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every integer coordinate i has a positive natural period p for which y(i + kp) = y(i) for all integers k. This condition allows a globally periodic point. In particular it is only the coordinate periodicity part of the source's Toeplitz condition, which also requires nonperiodicity.

**Theorem 1.2 (An actual aligned intersection).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/AlignedTowerLimit.aligned_intersection_nonempty`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/AlignedTowerLimit.aligned_intersection_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let W(n) be two nonempty binary words at each natural level. If successive aligned visible images are nested, their intersection is nonempty. The compact image at each level consists of readouts of actual marked tilings with a boundary at physical zero. Compactness and nesting suffice: no recognizability or compatible choice of marked representations is assumed. The compactness input is TwoRunRefinement.alignedConfigurations_compact_nonempty.

**Theorem 1.3 (Common ends cover signed coordinates).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/AlignedTowerLimit.has_periodic_coordinates_of_aligned_tower`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/AlignedTowerLimit.has_periodic_coordinates_of_aligned_tower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose both words at level n have the same positive length L(n), the lengths are unbounded, W(n,false) prefixes both words at level n+1, and W(n,true) suffixes both. Any point in all aligned visible images has periodic coordinates. For a physical coordinate i choose n with L(n) greater than its absolute value, and an actual aligned level-(n+1) tiling reading the point. At a nonnegative i the phase is i and lies in the common prefix. At i = -(m+1) the signed remainder is L(n+1)-1-m; the common suffix is read at index L(n)-1-m. The prefix also implies L(n) ≤ L(n+1). The List prefix and suffix element lemmas identify the two upper symbols, and tiled_common_column_periodic gives all integer multiples of the positive period L(n+1). Zero uses prefix index zero.

**Theorem 1.4 (A limit with periodic coordinates).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/AlignedTowerLimit.exists_aligned_periodic_point`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/AlignedTowerLimit.exists_aligned_periodic_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Combining the compact intersection with the common-end criterion produces a binary point in every aligned tiling image with periodic coordinates. This is a consumed composition of the preceding results: the actual balanced construction below uses it. Image membership also gives membership in the ordinary tiled subshift at every level. It does not require continuity or injectivity of any refinement map.

**Definition 1.5 (The equal-height balanced factorial construction).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/AlignedTowerLimit.alignedPeriodicPoint`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/AlignedTowerLimit.alignedPeriodicPoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The supplied point uses W(n,a) = Balanced.balancedWord n a and L(n) = Balanced.height n. The existing word length theorem and positive height theorem provide equal positive lengths, and height_lower_bound gives unboundedness. The actual two-run refinement uses l(a) = (if a then 1 else 2) times (n+1)! and r(a) = (if a then 2 else 1) times (n+1)!. Its alignedConfigurations_subset theorem supplies nesting; balancedWord_prefix_false and balancedWord_suffix_true supply the common ends. The resulting subtype contains an actual binary configuration with an origin-aligned marked tiling at every balanced level and periodicity at every signed coordinate. This is an application of the generic criterion, not a separate new mathematical theorem. The construction concerns these equal-height balanced words only. Nonperiodicity, regularity, essential periods and strict ergodicity require their own proofs; no statement about the older unequal-length words follows.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/AlignedTowerLimit.HasPeriodicCoordinates`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/AlignedTowerLimit.alignedPeriodicPoint`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/AlignedTowerLimit.aligned_intersection_nonempty`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/AlignedTowerLimit.exists_aligned_periodic_point`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/AlignedTowerLimit.has_periodic_coordinates_of_aligned_tower`
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedWords](BalancedWords.md)
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/EqualLengthTiling](EqualLengthTiling.md)
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement](TwoRunRefinement.md)
