# Balance of Lower Mechanical Words

## Abstract

Extract the reusable floor kernel behind lower mechanical word balance.

Fix a real slope alpha in the half-open interval from zero to one and an arbitrary real intercept rho. Irrationality is not required for any result in this module.

**Definition 1.1 (Lower mechanical letters are consecutive floor differences).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalBalance.lowerMechanicalLetter`

*Formalization.* `D5/S1/Words/Mechanical/MechanicalBalance.lowerMechanicalLetter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The letter at n is the floor at rho+(n+1)alpha minus the floor at rho+n alpha. Its Boolean readout is true exactly when this integer is one.

**Theorem 1.2 (Every letter is zero or one).**

$$\operatorname{lowerMechanicalLetter}\left(\mathit{alpha}, \mathit{rho}, n\right) = 0 \lor \operatorname{lowerMechanicalLetter}\left(\mathit{alpha}, \mathit{rho}, n\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalBalance.lowerMechanicalLetter_eq_zero_or_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two standard floor-add inequalities trap each consecutive floor difference between zero and one.

**Theorem 1.3 (Window counts telescope to endpoint floors).**

$$\operatorname{windowTrueCount}\left(\mathit{alpha}, \mathit{rho}, i, n\right) = \operatorname{floor}\left(\mathit{rho} + \left(i + n\right) \cdot \mathit{alpha}\right) - \operatorname{floor}\left(\mathit{rho} + i \cdot \mathit{alpha}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalBalance.lowerMechanicalWindowTrueCount_eq_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Replacing each Boolean indicator by its zero-or-one letter makes the finite sum telescope, leaving only the two floors at the window endpoints.

**Theorem 1.4 (Equal-length windows are balanced by one).**

$$\operatorname{windowTrueCount}\left(\mathit{alpha}, \mathit{rho}, i, n\right) - \operatorname{windowTrueCount}\left(\mathit{alpha}, \mathit{rho}, j, n\right) = 0 - 1 \lor \left(\operatorname{windowTrueCount}\left(\mathit{alpha}, \mathit{rho}, i, n\right) - \operatorname{windowTrueCount}\left(\mathit{alpha}, \mathit{rho}, j, n\right) = 0 \lor \operatorname{windowTrueCount}\left(\mathit{alpha}, \mathit{rho}, i, n\right) - \operatorname{windowTrueCount}\left(\mathit{alpha}, \mathit{rho}, j, n\right) = 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalBalance.lowerMechanicalWord_balanced_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of starting positions, the integer true-count difference of equal-length windows has absolute value at most one.

## References

- Truth anchor: `D5/S1/Words/Mechanical/MechanicalBalance.lowerMechanicalLetter`
- Truth anchor: `D5/S1/Words/Mechanical/MechanicalBalance.lowerMechanicalLetter_eq_zero_or_one`
- Truth anchor: `D5/S1/Words/Mechanical/MechanicalBalance.lowerMechanicalWindowTrueCount_eq_floor`
- Truth anchor: `D5/S1/Words/Mechanical/MechanicalBalance.lowerMechanicalWord_balanced_one`
