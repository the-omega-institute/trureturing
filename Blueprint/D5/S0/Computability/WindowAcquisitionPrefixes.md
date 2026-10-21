# Physical prefixes and original Horner coordinates

## Abstract

Physical prefixes and original Horner coordinates.

Every actual input window, including each high null, increments the counter. The finite guard compares the previous higher window low bit with the current upper bit. The saved bit becomes the current low bit. The independent unit guard is tested before terminal arithmetic.

The original composition applies the matrix with rows (1,2) and (2,3), then the five displacements (0,0), (1,0), (0,1), (2,1) and (1,1). Prefix coordinates and actual count are related at physical prefix times. The unit is included separately in the final numeral.

**Theorem 1.1 (source prefix registers).**

Lean statement: `D5/S0/Computability/WindowAcquisitionPrefixes.source_prefix_registers`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/WindowAcquisitionPrefixes.source_prefix_registers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With all declared parameters and hypotheses, the exact statement is: source_prefix_registers (pre suf : List Window) (e : Bool) (hg : D5.S3.Arith.ZeckendorfFutureKernel.legal false (NativeContinuation.NullReplyFiber.highBits ((pre ++ suf).map letter))) : ∃ T : ℕ, T ≤ 4 + pre.length * (15 * (pre ++ suf).length + 46) ∧ run (initial (pre ++ suf) e) T = boundary (inputSource (pre ++ suf) e) pre.length (columnsAfter [zeros] pre) 0 (.source (seamAfter false pre)) ∧ pair (columnsAfter [zeros] pre) = NativeContinuation.JointLaw.composition (pre.map letter) ∧ valueCount (columnsAfter [zeros] pre) = pre.length ∧ (columnsAfter [zeros] pre).length ≤ 1 + 3 * pre.length ∧ ∀ n ≤ T, Frame (inputSource (pre ++ suf) e) (pre ++ suf).length (3 * (pre ++ suf).length + 5) (run (initial (pre ++ suf) e) n)

**Theorem 1.2 (source unit entry).**

Lean statement: `D5/S0/Computability/WindowAcquisitionPrefixes.source_unit_entry`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/WindowAcquisitionPrefixes.source_unit_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With all declared parameters and hypotheses, the exact statement is: source_unit_entry (w : List Window) (e : Bool) (hg : D5.S3.Arith.ZeckendorfFutureKernel.legal false (NativeContinuation.NullReplyFiber.highBits (w.map letter) ++ [e])) : ∃ T : ℕ, T ≤ 6 + w.length * (15*w.length+46) ∧ run (initial w e) T = boundary (inputSource w e) w.length (columnsAfter [zeros] w) 1 (.finishScan (if e then 1 else 0) false) ∧ pair (columnsAfter [zeros] w) = NativeContinuation.JointLaw.composition (w.map letter) ∧ valueCount (columnsAfter [zeros] w) = w.length ∧ (columnsAfter [zeros] w).length ≤ 1+3*w.length ∧ ∀ n ≤ T, Frame (inputSource w e) w.length (3*w.length+5) (run (initial w e) n)

## References

- Truth anchor: `D5/S0/Computability/WindowAcquisitionPrefixes.source_prefix_registers`
- Truth anchor: `D5/S0/Computability/WindowAcquisitionPrefixes.source_unit_entry`
- Dependency: [D5/S0/Computability/WindowAcquisitionCore](WindowAcquisitionCore.md)
