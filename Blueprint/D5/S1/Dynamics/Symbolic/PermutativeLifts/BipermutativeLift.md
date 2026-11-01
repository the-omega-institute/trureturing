# The entire bipermutative lift as a finite skew product

## Abstract

The entire bipermutative lift as a finite skew product.

**Theorem 1.1 (Sliding codes commute with integer shifts).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.code_shift`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.code_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual finite-window block code commutes with every signed integer shift.

**Definition 1.2 (The full integer lift action).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.integerShift`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.integerShift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The entire inverse image of any subshift carries the inherited integer shift. Subshift invariance and the public code-shift law supply membership without a new reconstruction proof.

**Definition 1.3 (Construction).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.fullLiftHomeomorph`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.fullLiftHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a code of length k+2 over any finite discrete alphabet, the fibre is exactly the set Fin(k+1) to A of actual prefixes. Bijectivity in both endpoints makes the prefix update a permutation. Integer iterates reconstruct every two-sided preimage in both directions. Coordinates consisting of the coded image and the prefix give a homeomorphism of the entire inverse image to the base times that prefix fibre, conjugating the shift to the actual prefix permutation cocycle.

**Theorem 1.4 (Result).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.full_lift_conjugacy`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.full_lift_conjugacy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a code of length k+2 over any finite discrete alphabet, the fibre is exactly the set Fin(k+1) to A of actual prefixes. Bijectivity in both endpoints makes the prefix update a permutation. Integer iterates reconstruct every two-sided preimage in both directions. Coordinates consisting of the coded image and the prefix give a homeomorphism of the entire inverse image to the base times that prefix fibre, conjugating the shift to the actual prefix permutation cocycle.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.code_shift`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.fullLiftHomeomorph`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.full_lift_conjugacy`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.integerShift`
