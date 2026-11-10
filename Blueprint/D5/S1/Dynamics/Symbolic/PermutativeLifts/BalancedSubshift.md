# Recognizable balanced factorial subshift

## Abstract

Recognizable balanced factorial subshift.

**Definition 1.1 (Actual physical refinement).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.refineBalancedTiling`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.refineBalancedTiling` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A marked level-(n+1) balanced tiling refines to a level-n tiling by the two actual runs of child words. Refinement retains the same physical integer coordinate, rather than replacing the point with a reindexed block sequence.

**Theorem 1.2 (Refinement preserves the point).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.read_refineBalancedTiling`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.read_refineBalancedTiling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reading the refined marked tiling gives exactly the original binary configuration at every integer coordinate. The proof reuses the generic two-run coordinate-read theorem.

**Theorem 1.3 (Recognizable parent boundaries).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.refineBalancedTiling_boundary_iff`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.refineBalancedTiling_boundary_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the refined physical tiling, a parent boundary is exactly a child boundary where the preceding child has type true and the current child has type false. Both factorial runs are positive. This recovers boundaries from actual lower-level type transitions.

**Theorem 1.4 (Unique marked presentation).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.balancedReadTiling_injective`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.balancedReadTiling_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each level the readout map on actual marked balanced tilings is injective. The induction identifies the lower tilings, recovers the parent boundary sets, and uses equal positive lengths together with distinct upper words to recover every marked state. Equal heights are not used as a substitute for distinct words.

**Theorem 1.5 (Nested visible subshifts).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.balanced_subshift_succ_subset`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.balanced_subshift_succ_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every visible level-(n+1) balanced tiling reads a visible level-n tiling, using the actual refinement and its readout equality.

**Definition 1.6 (The actual compact intersection).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.balancedSubshift`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.balancedSubshift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier is the intersection over all natural levels of the visible images of actual balanced marked tilings. It is closed and shift invariant. It is not a predicate assuming minimality, recurrence or aperiodicity.

**Theorem 1.7 (A nonempty compact space).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.balanced_subshift_nonempty`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.balanced_subshift_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nested nonempty compact visible images have a point in their intersection. The associated BalancedPoint subtype has Nonempty and CompactSpace instances.

**Definition 1.8 (The unique compatible decoder).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.decode`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.decode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The decoder selects a marked level-n presentation from actual intersection membership. Its readout is the original point, and recognizability makes the selected presentation unique.

**Theorem 1.9 (Exact decoder readout).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.read_decode`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.read_decode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual BalancedPoint, reading its level-n decoder gives the same binary point at all integer coordinates.

**Theorem 1.10 (Continuous tower coordinates).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.continuous_decode`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.continuous_decode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every level decoder is continuous. The readout is continuous from a compact marked-tiling space into the Hausdorff full shift, and injectivity identifies closed decoder preimages with preimages of compact readout images.

**Theorem 1.11 (Shift compatibility).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.decode_shift`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.decode_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Decoding an integer shift is exactly the same as shifting the marked decoder. Both readouts agree and the readout map is injective.

**Theorem 1.12 (Compatibility between levels).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.refine_decode`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.refine_decode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Refining the level-(n+1) decoder gives the level-n decoder of the very same point. This equality follows from actual readouts and recognizability, without an extra compatibility assumption.

**Theorem 1.13 (No positive global period).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.balanced_no_positive_period`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.balanced_no_positive_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every point in the actual intersection has no positive natural shift period. A hypothetical period p would preserve its unique sufficiently high marked tiling while moving a boundary strictly into a tile of length greater than p, contradicting the internal offset.

**Theorem 1.14 (Infinitely many points).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.balanced_nat_orbit_injective`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.balanced_nat_orbit_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nonnegative integer orbit of every point is injective, by cancellation of a common shift and the absence of positive periods. Nonemptiness then supplies the Infinite BalancedPoint instance. No claim about the older unequal-length factorial subshift is made. The public theorem escape registrations are unfinished under https://github.com/the-omega-institute/trureturing/issues/24726; the current scoped report verifies the Lean declarations and standard axiom closure, and does not constitute declared_validated four-slot audit evidence.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.balancedReadTiling_injective`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.balancedSubshift`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.balanced_nat_orbit_injective`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.balanced_no_positive_period`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.balanced_subshift_nonempty`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.balanced_subshift_succ_subset`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.continuous_decode`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.decode`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.decode_shift`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.read_decode`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.read_refineBalancedTiling`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.refineBalancedTiling`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.refineBalancedTiling_boundary_iff`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift.refine_decode`
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedWords](BalancedWords.md)
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/EqualLengthTiling](EqualLengthTiling.md)
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement](TwoRunRefinement.md)
