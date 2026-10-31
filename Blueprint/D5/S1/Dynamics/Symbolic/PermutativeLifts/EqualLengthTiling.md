# Equal-length marked tiling phases and recognizability

## Abstract

Equal-length marked tiling phases and recognizability.

**Theorem 1.1 (Two-sided phase).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EqualLengthTiling.tiled_offset_phase`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/EqualLengthTiling.tiled_offset_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two binary words of a common positive length L, the marked offset at every integer i is the nonnegative remainder of i plus the offset at zero modulo L. Comparing the tiling with a periodic tiling of one word propagates offset equality both forwards and backwards. Thus translation by any integer multiple of L preserves the phase, and the boundary set is one residue class.

**Theorem 1.2 (Identification from symbols and boundaries).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EqualLengthTiling.equal_length_tiling_eq_of_read_boundaries`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/EqualLengthTiling.equal_length_tiling_eq_of_read_boundaries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the two words have equal lengths and are distinct as words. Two actual marked tilings with identical visible sequences and identical boundary sets are equal. Boundaries first identify every offset. Starting at the common preceding boundary, forward traversal reads every letter of the corresponding words; equality of those words identifies their types. Distinct word lengths are not required.

**Theorem 1.3 (Periodic common columns).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EqualLengthTiling.tiled_common_column_periodic`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/EqualLengthTiling.tiled_common_column_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the two words agree at the marked offset of a coordinate, its visible symbol is unchanged by every integer multiple of their common length. This holds for arbitrary origin phase. For a tiling with a boundary at zero, each residue at which the words agree therefore gives a fixed symbol throughout that residue class. The conclusion covers negative coordinates and negative multiples as well.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EqualLengthTiling.equal_length_tiling_eq_of_read_boundaries`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EqualLengthTiling.tiled_common_column_periodic`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EqualLengthTiling.tiled_offset_phase`
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/MarkedTiling](MarkedTiling.md)
