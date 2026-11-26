# The entire bipermutative lift as a finite skew product

## Abstract

The entire bipermutative lift as a finite skew product.

**Definition 1.1 (Reconstruction from prefix permutations).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.equivOfPrefixPerm`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.equivOfPrefixPerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an arbitrary alphabet, suppose a family of prefix permutations agrees pointwise with the native prefix step. The skew product shifts the entire output by one and applies the corresponding permutation to the literal prefix. Its signed integer iterates define overlapping prefixes and hence one physical source sequence. This construction is shared by the finite-alphabet equivalence and by arbitrary-alphabet recovery after the prefix permutations have been constructed.

**Theorem 1.2 (Reconstruction realizes the prescribed coordinates).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.coordinates_reconstruct_of_prefix_perm`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.coordinates_reconstruct_of_prefix_perm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every supplied prefix permutation agrees with the native prefix step, reconstructing an output-prefix pair and then taking its native coordinates returns that pair. Prefix overlap identifies each reconstructed physical window; the right-end equation gives its output letter.

**Theorem 1.3 (Reconstruction recovers every source).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.reconstruct_coordinates_of_prefix_perm`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.reconstruct_coordinates_of_prefix_perm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same prefix permutations, reconstructing the native coordinates of an existing source returns the source. The coordinate map intertwines both forward and backward source shifts with the skew product, so every reconstructed prefix is the corresponding physical prefix.

**Theorem 1.4 (Sliding codes commute with integer shifts).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.code_shift`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.code_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual finite-window block code commutes with every signed integer shift.

**Definition 1.5 (The full integer lift action).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.integerShift`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.integerShift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The entire inverse image of any subshift carries the inherited integer shift. Subshift invariance and the public code-shift law supply membership without a new reconstruction proof.

**Definition 1.6 (Construction).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.fullLiftHomeomorph`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.fullLiftHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a code of length k+2 over any finite discrete alphabet, the fibre is exactly the set Fin(k+1) to A of actual prefixes. Bijectivity in both endpoints makes the prefix update a permutation. Integer iterates reconstruct every two-sided preimage in both directions. Coordinates consisting of the coded image and the prefix give a homeomorphism of the entire inverse image to the base times that prefix fibre, conjugating the shift to the actual prefix permutation cocycle.

**Theorem 1.7 (Result).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.full_lift_conjugacy`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.full_lift_conjugacy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a code of length k+2 over any finite discrete alphabet, the fibre is exactly the set Fin(k+1) to A of actual prefixes. Bijectivity in both endpoints makes the prefix update a permutation. Integer iterates reconstruct every two-sided preimage in both directions. Coordinates consisting of the coded image and the prefix give a homeomorphism of the entire inverse image to the base times that prefix fibre, conjugating the shift to the actual prefix permutation cocycle.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.code_shift`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.coordinates_reconstruct_of_prefix_perm`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.equivOfPrefixPerm`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.fullLiftHomeomorph`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.full_lift_conjugacy`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.integerShift`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.reconstruct_coordinates_of_prefix_perm`
