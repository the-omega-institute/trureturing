# A concrete S4 action on the three pairings of four vertices

## Abstract

The finite action on opposite edge pairs

The six edge slots are 01, 02, 03, 23, 13, and 12. The three pair slots record the opposite edge pairings 01|23, 02|13, and 03|12. For each permutation of the four vertices, inducedPairAction records the resulting permutation of these three pair slots.

**Theorem 1.1 (Every induced action is a bijection).**

Lean statement: `D5/S3/Geometry/Hyperideal/S4OppositePairAction.induced_pair_action_bijective`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/S4OppositePairAction.induced_pair_action_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite kernel computation verifies that the action induced by every permutation of the four vertices is bijective on the three opposite pair slots.

This is a concrete finite action calculation. It does not assert a global geometric automorphism or a general theorem about all face pairings.

**Theorem 1.2 (The induced action has six distinct outputs).**

Lean statement: `D5/S3/Geometry/Hyperideal/S4OppositePairAction.opposite_pair_action_image_card`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/S4OppositePairAction.opposite_pair_action_image_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite image of inducedPairAction has cardinality six. Thus the explicit four-vertex action reaches all six possible permutations of the three pair slots.

The computation concerns this displayed finite table only. It does not by itself identify a geometric realization or establish an abstract quotient map beyond the enumerated action.

**Theorem 1.3 (Four explicit permutations act trivially).**

Lean statement: `D5/S3/Geometry/Hyperideal/S4OppositePairAction.four_named_kernel_elements`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/S4OppositePairAction.four_named_kernel_elements` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity and the three displayed double swaps (01)(23), (02)(13), and (03)(12) all fix the three opposite pair slots. The finite proof also checks that these four vertex permutations are pairwise distinct.

This supplies four explicit elements of the kernel of the displayed action. A separate exact kernel classification and the associated abstract group identification are outside this module. The faithful source-bound escape audit remains unfinished under https://github.com/the-omega-institute/trureturing/issues/19015.

**Theorem 1.4 (A vertex transposition swaps two pair slots).**

Lean statement: `D5/S3/Geometry/Hyperideal/S4OppositePairAction.transposition_generates_pair_swap`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/S4OppositePairAction.transposition_generates_pair_swap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The transposition exchanging vertices 0 and 1 induces the pair-slot permutation [0, 2, 1].

**Theorem 1.5 (A vertex three-cycle rotates the pair slots).**

Lean statement: `D5/S3/Geometry/Hyperideal/S4OppositePairAction.three_cycle_generates_pair_cycle`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/S4OppositePairAction.three_cycle_generates_pair_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cycle 0 -> 1 -> 2 -> 0 induces the pair-slot permutation [2, 0, 1]. Together with the transposition computation and the six-element image count, this gives the concrete finite S4-to-three-slot interface.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/S4OppositePairAction.four_named_kernel_elements`
- Truth anchor: `D5/S3/Geometry/Hyperideal/S4OppositePairAction.induced_pair_action_bijective`
- Truth anchor: `D5/S3/Geometry/Hyperideal/S4OppositePairAction.opposite_pair_action_image_card`
- Truth anchor: `D5/S3/Geometry/Hyperideal/S4OppositePairAction.three_cycle_generates_pair_cycle`
- Truth anchor: `D5/S3/Geometry/Hyperideal/S4OppositePairAction.transposition_generates_pair_swap`
