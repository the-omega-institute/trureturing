# Zeckendorf-Beatty Bridge

## Abstract

Identify the least Zeckendorf digit with the shifted golden Beatty letter.

For a canonical Zeckendorf representation, the conjugate-power error lies on opposite sides of phi^(-3) according to whether index 2 is absent or present. This is exactly the existing golden mechanical window test.

**Theorem 1.1 (The least digit is the shifted mechanical letter).**

$$\operatorname{leastDigitAbsent}\left(i\right) = \operatorname{goldenMechanicalLetterIsOne}\left(i + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ZeckendorfBeattyBridge.zeckendorf_beatty_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural i, index 2 is absent from wdigits i if and only if goldenMechanicalLetter(i+1) equals one. The shift is part of the statement and is not absorbed into either frozen definition.

**Theorem 1.2 (The Fibonacci word has an explicit Beatty floor test).**

$$\operatorname{fibWord}\left(Q\right) = \operatorname{ofFn}\left(\operatorname{shiftedGoldenBeattyFloorTest}\left(Q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ZeckendorfBeattyBridge.fibWord_eq_beatty_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each valid position i, the Boolean letter is true exactly when floor((i+2)/phi)-floor((i+1)/phi)=1. This follows by rewriting the frozen least-Zeckendorf-digit formula through the bridge above.

## References

- Truth anchor: `D5/S1/Words/ZeckendorfBeattyBridge.fibWord_eq_beatty_floor`
- Truth anchor: `D5/S1/Words/ZeckendorfBeattyBridge.zeckendorf_beatty_bridge`
- Dependency: [D5/S0/Tower/GoldenGapZeckendorf](../../S0/Tower/GoldenGapZeckendorf.md)
- Dependency: [D5/S1/Words/GoldenMechanicalWord](GoldenMechanicalWord.md)
