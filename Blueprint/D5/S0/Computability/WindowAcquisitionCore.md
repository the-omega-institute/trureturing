# Window arithmetic by local actions

## Abstract

Window arithmetic by local actions.

Eight tracks have fixed origins. A transition reads one finite symbol, writes one finite symbol, or moves one head by one cell. Work is blank initially. The five input letters encode 000, 100, 010, 101 and 001 with low bit printed first. The source order is high to low and its independent unit letter ends acquisition.

The finite carry updates the two binary Horner coordinates and the binary window count together. The scan writes actual bits, flushes at most three extra columns, tests the home marker and pays for its backward head motion. Safe preserves the source tape, parked source head and unused tapes, and bounds the moving work head throughout the attained run.

**Theorem 1.1 (update scan return).**

Lean statement: `D5/S0/Computability/WindowAcquisitionCore.update_scan_return`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/WindowAcquisitionCore.update_scan_return` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With all declared parameters and hypotheses, the exact statement is: update_scan_return (source : ℤ → Symbol) (p : ℤ) (bs : List Bits) (previous : Bool) (carry : Carry) : ∃ T : ℕ, T ≤ 5 * bs.length + 18 ∧ run (boundary source p bs 1 (.scan previous carry)) T = boundary source p (updated carry bs) 0 (.sourceMove previous) ∧ (updated carry bs).length ≤ bs.length + 3 ∧ ∀ t ≤ T, Safe source p (bs.length + 3) (run (boundary source p bs 1 (.scan previous carry)) t)

## References

- Truth anchor: `D5/S0/Computability/WindowAcquisitionCore.update_scan_return`
- Dependency: [D5/S0/Computability/Coding/PhysicalSixParser](Coding/PhysicalSixParser.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw](../../S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.md)
