# Sparse disagreement and finite windows

## Abstract

Finite phase control of disagreement in equal-height marked tilings.

**Definition 1.1 (Exceptional phases).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/SparseDisagreement.badPhases`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/SparseDisagreement.badPhases` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a positive height L, let D be a finite set of residues modulo L. A phase is exceptional for the signed window starting at t with length r when adding one of t, t+1, ..., t+r-1 lands in D. The exceptional set is the union of the corresponding r translates of D.

**Theorem 1.2 (Exceptional-phase count).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/SparseDisagreement.badPhases_card_le`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/SparseDisagreement.badPhases_card_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The number of exceptional phases is at most r times the size of D. The finite-union bound counts at most one copy of D per window coordinate, allowing overlap between translates and including r=0.

**Theorem 1.3 (Physical cyclic phase law).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/SparseDisagreement.offset_cast`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/SparseDisagreement.offset_cast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Casting the two-sided physical offset law to the finite cyclic group turns the integer remainder formula into addition of the translated coordinate. This bridge is shared by the finite-window argument and the actual invariant-measure phase factor.

**Theorem 1.4 (Agreement across all seams).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/SparseDisagreement.same_phase_window`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/SparseDisagreement.same_phase_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take two actual marked tilings by two Boolean words of the same positive length. Their physical offsets evolve by the cyclic phase law from EqualLengthTiling. If their offsets at zero agree and this initial phase avoids the translates of the words' differing columns, the two readouts agree at every coordinate of the window. The conclusion covers negative starting coordinates and windows crossing any number of tile boundaries; it assumes neither a common tile type nor a choice of a point in each phase fibre.

**Theorem 1.5 (Literal columns and list mismatch).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/SparseDisagreement.wordDisagreements_card`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/SparseDisagreement.wordDisagreements_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The differing-column set consists precisely of residues whose aligned letters differ. Its cardinality equals the list mismatch count used by BalancedWords. This interface transports the exact combinatorial recurrence to the physical phase coordinates of actual tilings.

**Theorem 1.6 (Balanced exceptional-phase estimate).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/SparseDisagreement.balanced_badPhases_card_scaled`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/SparseDisagreement.balanced_badPhases_card_scaled` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the actual equal-height balanced factorial words at level n, the existing identity 3^n d(n)=h(n) gives 3^n times the number of exceptional phases at most r h(n). The integral estimate avoids division and rounding. It supplies the finite phase input for a separate invariant-measure cylinder argument; no existence or uniqueness of invariant measures is asserted in this module.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/SparseDisagreement.badPhases`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/SparseDisagreement.badPhases_card_le`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/SparseDisagreement.balanced_badPhases_card_scaled`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/SparseDisagreement.offset_cast`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/SparseDisagreement.same_phase_window`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/SparseDisagreement.wordDisagreements_card`
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedWords](BalancedWords.md)
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/EqualLengthTiling](EqualLengthTiling.md)
