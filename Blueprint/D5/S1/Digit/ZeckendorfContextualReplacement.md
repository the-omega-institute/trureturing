# Contextual Fibonacci Parity Replacement

## Abstract

A fourteen-digit contextual replacement preserves complete partial Fibonacci parity residuals.

**Definition 1.1 (Smaller replacement block).**

Lean statement: `D5/S1/Digit/ZeckendorfContextualReplacement.B0`

*Formalization.* `D5/S1/Digit/ZeckendorfContextualReplacement.B0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

B0 : List (Fin 2) is [0,0,0,1,0,0,1,0,1,0,1,0,0,0], the fourteen-digit MSD block 00010010101000.

**Definition 1.2 (Larger replacement block).**

Lean statement: `D5/S1/Digit/ZeckendorfContextualReplacement.B1`

*Formalization.* `D5/S1/Digit/ZeckendorfContextualReplacement.B1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

B1 : List (Fin 2) is [0,0,0,1,0,1,0,1,0,0,1,0,0,0], the fourteen-digit MSD block 00010101001000.

The source conventions are the padded most-significant-digit Fibonacci words of Moradi, Rampersad, and Shallit, arXiv:2603.21645v1. This bridge does not establish a state-count bound or settle Problem 1.

**Theorem 1.3 (Equality on every continuation).**

Lean statement: `D5/S1/Digit/ZeckendorfContextualReplacement.contextual_replacement`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/ZeckendorfContextualReplacement.contextual_replacement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete statement is `theorem contextual_replacement (H : ℕ) (p u : List (Fin 2)) (hH : 14 ≤ H) (huH : 14 + u.length ≤ H) (hlegal : NoAdjacentOnes (p ++ B1 ++ u)) : ZeckendorfRawWindow.residual (Nat.fib H) (p ++ B1 ++ u) = ZeckendorfRawWindow.residual (Nat.fib H) (p ++ B0 ++ u)`.

For H at least fourteen, arbitrary high context p and low context u with fourteen plus the length of u at most H, replacing 00010101001000 by 00010010101000 preserves the entire Option-valued residual at shift F_H. The same realized high and low supports are retained in all three carry regions. The equality includes the empty suffix, every longer suffix, and undefined execution on invalid suffixes.

## References

- Truth anchor: `D5/S1/Digit/ZeckendorfContextualReplacement.B0`
- Truth anchor: `D5/S1/Digit/ZeckendorfContextualReplacement.B1`
- Truth anchor: `D5/S1/Digit/ZeckendorfContextualReplacement.contextual_replacement`
- Dependency: [D5/S1/Digit/ZeckendorfCarryBarrier](ZeckendorfCarryBarrier.md)
- Dependency: [D5/S1/Digit/ZeckendorfRawWindow](ZeckendorfRawWindow.md)
