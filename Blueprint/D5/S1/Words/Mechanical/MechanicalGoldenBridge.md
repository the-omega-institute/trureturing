# Golden Bridge for Lower Mechanical Words

## Abstract

Connect the reusable lower-mechanical floor kernel to the frozen golden word.

Specialize the general lower-mechanical kernel at slope one over the golden ratio and intercept zero. The existing one-index shift is retained, and irrationality is not used by the balance proof.

**Theorem 1.1 (The golden slope specializes the generic letter).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalGoldenBridge.lowerMechanicalLetter_golden`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalGoldenBridge.lowerMechanicalLetter_golden` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the frozen golden slope and zero intercept, the generic floor difference is exactly the existing golden mechanical letter.

**Theorem 1.2 (The generic readout agrees with the shifted golden word).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalGoldenBridge.lowerMechanicalWord_golden`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalGoldenBridge.lowerMechanicalWord_golden` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Boolean generic readout agrees with the frozen golden word at the repository's established one-index shift.

**Theorem 1.3 (Golden windows are shifted generic windows).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalGoldenBridge.goldenWindowTrueCount_eq_lowerMechanicalWindowTrueCount`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalGoldenBridge.goldenWindowTrueCount_eq_lowerMechanicalWindowTrueCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen golden true-count function is equal to the generic lower-mechanical count beginning one position later.

**Theorem 1.4 (Frozen golden balance follows from the generic theorem).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalGoldenBridge.goldenWord_balanced_one_mechanical`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalGoldenBridge.goldenWord_balanced_one_mechanical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing golden balanced-one statement is obtained directly from the generic equal-window theorem through the shift bridge.

## References

- Truth anchor: `D5/S1/Words/Mechanical/MechanicalGoldenBridge.goldenWindowTrueCount_eq_lowerMechanicalWindowTrueCount`
- Truth anchor: `D5/S1/Words/Mechanical/MechanicalGoldenBridge.goldenWord_balanced_one_mechanical`
- Truth anchor: `D5/S1/Words/Mechanical/MechanicalGoldenBridge.lowerMechanicalLetter_golden`
- Truth anchor: `D5/S1/Words/Mechanical/MechanicalGoldenBridge.lowerMechanicalWord_golden`
- Dependency: [D5/S1/Words/Mechanical/MechanicalBalance](MechanicalBalance.md)
