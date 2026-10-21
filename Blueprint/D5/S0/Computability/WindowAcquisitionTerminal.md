# Paid terminal arithmetic and persistent storage

## Abstract

Paid terminal arithmetic and persistent storage.

Terminal arithmetic scans the packed column to form twice the first coordinate plus three times the second plus the independent unit. Carry propagation, source-unit reading, zero testing and the return to origin are local actions.

Visited storage includes the supplied input, all origins and the union of every earlier head position, including cells erased or left blank. Charge also counts a fixed finite symbol code, the complete fixed control program, current control and descriptions of every head. The all-prefix frame bounds historical visits in a common interval.

**Theorem 1.1 (scan return).**

Lean statement: `D5/S0/Computability/WindowAcquisitionTerminal.scan_return`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/WindowAcquisitionTerminal.scan_return` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With all declared parameters and hypotheses, the exact statement is: scan_return (source : ℤ → Symbol) (p : ℤ) (bs : List Bits) (carry : Fin 5) (seen : Bool) : ∃ T : ℕ, T ≤ 5 * bs.length + 18 ∧ run (boundary source p bs 1 (.finishScan carry seen)) T = boundary source p (finished carry bs) 0 (if seen || hasN (finished carry bs) then .done else .reject) ∧ (finished carry bs).length ≤ bs.length + 3 ∧ ∀ t ≤ T, Safe source p (bs.length + 3) (run (boundary source p bs 1 (.finishScan carry seen)) t)

**Theorem 1.2 (prefix charged bound).**

Lean statement: `D5/S0/Computability/WindowAcquisitionTerminal.prefix_charged_bound`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/WindowAcquisitionTerminal.prefix_charged_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With all declared parameters and hypotheses, the exact statement is: prefix_charged_bound (w : List Window) (e : Bool) (T : ℕ) (hf : ∀ n ≤ T, Frame (inputSource w e) w.length (3*w.length+5) (run (initial w e) n)) : ∀ n ≤ T, chargedBits w e n ≤ (programCode.length + Fintype.card Control + 64*(Fintype.card Symbol+1)) * (w.length+1)

## References

- Truth anchor: `D5/S0/Computability/WindowAcquisitionTerminal.prefix_charged_bound`
- Truth anchor: `D5/S0/Computability/WindowAcquisitionTerminal.scan_return`
- Dependency: [D5/S0/Computability/WindowAcquisitionPrefixes](WindowAcquisitionPrefixes.md)
