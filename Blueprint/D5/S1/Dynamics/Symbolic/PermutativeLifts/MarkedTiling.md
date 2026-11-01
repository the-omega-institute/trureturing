# Compact spaces of marked block tilings

## Abstract

Compact spaces of marked block tilings.

**Definition 1.1 (Construction).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/MarkedTiling.MarkedTiling`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/MarkedTiling.MarkedTiling` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A marked state records the actual binary block type and its physical offset. Adjacent states either advance inside the same block or cross from its last letter to the start of a new block. The closed space of such integer-indexed states is compact. Reading letters gives the entire compact tiling subshift. If the two block lengths differ, equality of all boundary positions determines the marked tiling.

**Theorem 1.2 (Reading a specified coordinate).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/MarkedTiling.readTile_of_coordinates`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/MarkedTiling.readTile_of_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When a marked state's type is a and its physical offset is p, reading that state gives the p-th letter of W(a). The same declaration serves the finite-window proofs and the equal-length tiling proofs.

**Theorem 1.3 (Result).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/MarkedTiling.tiled_eq_of_boundaries`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/MarkedTiling.tiled_eq_of_boundaries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A marked state records the actual binary block type and its physical offset. Adjacent states either advance inside the same block or cross from its last letter to the start of a new block. The closed space of such integer-indexed states is compact. Reading letters gives the entire compact tiling subshift. If the two block lengths differ, equality of all boundary positions determines the marked tiling.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/MarkedTiling.MarkedTiling`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/MarkedTiling.readTile_of_coordinates`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/MarkedTiling.tiled_eq_of_boundaries`
