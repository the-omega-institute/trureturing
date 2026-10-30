# Canonical trimming and paid rewinds

## Abstract

Canonical trimming and paid rewinds.

Starting from a blank target at its origin, the fixed program writes the home marker and copies one actual packed lane. It walks backwards to erase all high zero bits, preserves the highest one when present, and inserts a single zero bit for value zero. An explicit end marker is written.

Both packed and target heads return to their fixed origins by paid unit moves. Each register phase has at most 32 times the sum of the packed length and one, in local actions. It preserves the selected numeric value and every unrelated tape and head throughout its frame.

**Theorem 1.1 (one register).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowRegisterTrim.one_register`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowRegisterTrim.one_register` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With all declared parameters and hypotheses, the exact statement is: one_register (m : Track → ℤ → Symbol) (h : Track → ℤ) (j : Lane) (bs : List Bits) (hw : h workTrack=0) (hj : h (target j)=0) (mw : m workTrack=word bs) (mj : m (target j)=fun _=>.blank) : ∃ T : ℕ, T ≤ 32*(bs.length+1) ∧ run (entry m h j) T = config m h j bs ((normalized (bs.map (select j))).map Symbol.unit ++ [.window .zero]) 0 0 (.laneDone j) ∧ (∀ n≤T, Frame m h j bs bs.length (run (entry m h j) n)) ∧ Nat.ofDigits 2 ((normalized (bs.map (select j))).map Bool.toNat)=bitValue (select j) bs ∧ (normalized (bs.map (select j))=[false] ∨ ∃ pre, normalized (bs.map (select j))=pre++[true])

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowRegisterTrim.one_register`
- Dependency: [D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowRegisterCore](WindowRegisterCore.md)
