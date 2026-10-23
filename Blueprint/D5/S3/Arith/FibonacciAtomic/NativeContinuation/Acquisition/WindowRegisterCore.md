# Fixed binary register tracks and copying

## Abstract

Fixed binary register tracks and copying.

Four separate register tracks have indices two through five. A register has a fixed origin marker, little-endian unit-bit symbols, an explicit end marker and blank cells beyond the end. The packed work tape stays on track one and the original input on track zero.

Copying reads a selected bit from each actual packed column and writes it to the target. Every read, write and head move is separate. The frame retains all unrelated tape cells and head positions while bounding both active heads.

**Theorem 1.1 (copy prefix).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowRegisterCore.copy_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowRegisterCore.copy_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With all declared parameters and hypotheses, the exact statement is: copy_prefix (m h j) (pre bs : List Bits) (L : ℕ) (hL : pre.length+bs.length ≤ L) : run (config m h j (pre++bs) ((pre.map (select j)).map Symbol.unit) (pre.length+1) (pre.length+1) (.scan j)) (4*bs.length) = config m h j (pre++bs) (((pre++bs).map (select j)).map Symbol.unit) (pre.length+bs.length+1) (pre.length+bs.length+1) (.scan j) ∧ ∀ n ≤ 4*bs.length, Frame m h j (pre++bs) L (run (config m h j (pre++bs) ((pre.map (select j)).map Symbol.unit) (pre.length+1) (pre.length+1) (.scan j)) n)

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowRegisterCore.copy_prefix`
- Dependency: [D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowAcquisitionPacked](WindowAcquisitionPacked.md)
