# Physical refinement of two-run word tilings

## Abstract

Physical refinement of two-run word tilings.

**Definition 1.1 (Two positive runs).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement.word`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement.word` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let W assign a nonempty binary word to each Boolean type, and let l and r assign positive integers to each parent type a. The upper word of type a is l(a) literal copies of W(false), followed by r(a) literal copies of W(true). At physical offset p, the cut is l(a) times the length of W(false). Before that cut the child type is false and its offset is p modulo the length of W(false); after it the child type is true and its offset is p minus the cut, modulo the length of W(true). Neither equality nor inequality of the two lower word lengths is required.

**Theorem 1.2 (Preservation of actual edges).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement.refineState_next`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement.refineState_next` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual upper TileNext edge maps to a lower TileNext edge. Within a parent, the upper types agree, so their cuts agree. The transition across the cut is the end of a false child followed by the start of a true child. Across a parent boundary, positivity places the old state in its true run and the new state in its false run, even when the two parents have different cuts. Thus pointwise refinement gives an actual map of bi-infinite marked tiling spaces.

**Theorem 1.3 (Parent boundary detection).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement.refineTiling_boundary_iff`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement.refineTiling_boundary_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every integer coordinate i of every actual upper marked tiling, its parent offset is zero if and only if the refined child type at i minus one is true and the refined child type at i is false. This identifies the parent boundaries from lower types; it does not assume or assert unique decoding from the visible binary configuration.

**Theorem 1.4 (Preservation of physical symbols).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement.readTiling_refineTiling`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement.readTiling_refineTiling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reading the refined marked tiling gives exactly the same binary configuration at every physical coordinate. The proof reads literal repeated words at the remainder of the physical offset. In particular every upper tiled configuration admits a lower tiling of the same visible symbols.

**Theorem 1.5 (Preservation of an aligned origin).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement.refineTiling_aligned_zero`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement.refineTiling_aligned_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the parent offset at physical coordinate zero is zero, the refined child offset there is also zero. This permits compatible constraints on the origin when forming nested spaces of aligned configurations. For a positive integer N, the construction applies to l(false) = 2N, l(true) = N, r(false) = N and r(true) = 2N. Unique decoding from visible binary symbols requires an additional recognizability argument.

**Theorem 1.6 (Nested tiling spaces).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement.tiledSubshift_subset`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement.tiledSubshift_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The tiled subshift for the upper words is a subset of the tiled subshift for W: refine a witnessing marked tiling and use equality of the physical readouts.

**Definition 1.7 (Configurations with an aligned origin).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement.alignedConfigurations`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement.alignedConfigurations` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The aligned configuration set consists of readouts of actual marked tilings whose offset at coordinate zero is zero. It is defined by an image, without assuming a unique marked representation.

**Theorem 1.8 (A nonempty compact aligned image).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement.alignedConfigurations_compact_nonempty`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement.alignedConfigurations_compact_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonempty words, the aligned configuration set is compact and nonempty. The zero-offset condition is closed in the compact marked tiling space, and the readout is continuous. A periodic tiling by W(false), started at its boundary, supplies a point.

**Theorem 1.9 (Nested aligned images).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement.alignedConfigurations_subset`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement.alignedConfigurations_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The aligned configuration set of the upper words is contained in the aligned configuration set of W. Refinement preserves both the visible readout and the zero offset at the physical origin. Consequently successive refinements supply the nesting needed for a compact intersection with a common aligned origin.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement.alignedConfigurations`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement.alignedConfigurations_compact_nonempty`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement.alignedConfigurations_subset`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement.readTiling_refineTiling`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement.refineState_next`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement.refineTiling_aligned_zero`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement.refineTiling_boundary_iff`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement.tiledSubshift_subset`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement.word`
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialRefinement](FactorialRefinement.md)
