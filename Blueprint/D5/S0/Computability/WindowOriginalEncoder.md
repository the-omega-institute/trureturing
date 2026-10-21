# Independent original padded input encoder

## Abstract

Independent original padded input encoder.

The original canonical occupied indices are Mathlib Zeckendorf indices, starting at F2=1. The independent unit is occupancy of index two. Window j groups indices 3j+3, 3j+4 and 3j+5 in low-to-high print order. W lists these windows from high to low. A finite renaming alone connects those five letters to the operational alphabet.

L is (the canonical dense word length plus one) divided by three using natural division; the independent unit is excluded from the windows. For every h at least L, W includes exactly h actual windows and retains every leading null. Its expanded high-to-low bit list with the final unit is exactly the padded canonical dense display. The existing canonical-language and numeric-value theorems supply legality and exact number; no length, legality or numeric identity is a new input premise.

**Theorem 1.1 (original bits).**

Lean statement: `D5/S0/Computability/WindowOriginalEncoder.original_bits`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/WindowOriginalEncoder.original_bits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With all declared parameters and hypotheses, the exact statement is: original_bits (h N : ℕ) : NativeContinuation.NullReplyFiber.highBits (W h N) ++ [bit N 0] = display N (3*h+1)

**Theorem 1.2 (padded windows).**

Lean statement: `D5/S0/Computability/WindowOriginalEncoder.padded_windows`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/WindowOriginalEncoder.padded_windows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With all declared parameters and hypotheses, the exact statement is: padded_windows (N h : ℕ) (hh : L N ≤ h) : W h N = List.replicate (h-L N) .zero ++ W (L N) N

**Theorem 1.3 (local source).**

Lean statement: `D5/S0/Computability/WindowOriginalEncoder.local_source`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/WindowOriginalEncoder.local_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With all declared parameters and hypotheses, the exact statement is: local_source (h N : ℕ) (hh : L N ≤ h) : (localWord h N).length=h ∧ legal false (NativeContinuation.NullReplyFiber.highBits ((localWord h N).map Original.letter) ++ [bit N 0]) ∧ Original.numeral (localWord h N) (bit N 0)=N

## References

- Truth anchor: `D5/S0/Computability/WindowOriginalEncoder.local_source`
- Truth anchor: `D5/S0/Computability/WindowOriginalEncoder.original_bits`
- Truth anchor: `D5/S0/Computability/WindowOriginalEncoder.padded_windows`
- Dependency: [D5/S0/Computability/WindowAcquisitionPacked](WindowAcquisitionPacked.md)
- Dependency: [D5/S1/Digit/GoldenBase4DenseInput](../../S1/Digit/GoldenBase4DenseInput.md)
- Dependency: [D5/S1/Digit/GoldenZeckendorfLanguage](../../S1/Digit/GoldenZeckendorfLanguage.md)
