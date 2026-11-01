# Continuous transfers for every finite action

## Abstract

Continuous transfers for every finite action.

**Theorem 1.1 (One-symbol prefix extension).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialCoboundary.holonomy_take_succ`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialCoboundary.holonomy_take_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Appending the next symbol to a taken prefix multiplies its holonomy on the left. This original generic monoid lemma is public for reuse by recognizable towers.

**Definition 1.2 (Generic tile-state transfer).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialCoboundary.stateTransfer`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialCoboundary.stateTransfer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The prefix product is defined for arbitrary binary tile words and a monoid. It is reused by both factorial and balanced towers.

**Theorem 1.3 (Generic tile-state transition).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialCoboundary.stateTransfer_next`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialCoboundary.stateTransfer_next` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If both complete tile words have identity holonomy, every legal marked-tile step multiplies the prefix product by its visible symbol on the left.

**Definition 1.4 (Construction).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialCoboundary.transfer`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialCoboundary.transfer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At a level where both block holonomies are identity, the prefix product from the recognizable block boundary gives a continuous transfer. Advancing inside a block adds the current letter permutation on the left. At a boundary, identity holonomy supplies the same equation. The finite set Q remains the actual action fibre; it is not replaced by a regular group action.

**Theorem 1.5 (Result).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialCoboundary.transfer_shift`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialCoboundary.transfer_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a level where both block holonomies are identity, the prefix product from the recognizable block boundary gives a continuous transfer. Advancing inside a block adds the current letter permutation on the left. At a boundary, identity holonomy supplies the same equation. The finite set Q remains the actual action fibre; it is not replaced by a regular group action.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialCoboundary.holonomy_take_succ`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialCoboundary.stateTransfer`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialCoboundary.stateTransfer_next`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialCoboundary.transfer`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialCoboundary.transfer_shift`
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialSubshift](FactorialSubshift.md)
