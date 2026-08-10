# Golden Gap Word from Zeckendorf Digits

## Abstract

Read each Fibonacci gap-word letter from the least Zeckendorf digit.

For every valid position i, the letter is large exactly when index 2 is absent from wdigits i. The right side is inlined in both public theorems; this node does not define a second public word object.

**Theorem 1.1 (The Fibonacci word is the least-digit test).**

$$\operatorname{fibWord}\left(Q\right) = \operatorname{ofFn}\left(\operatorname{leastZeckendorfDigitTest}\left(Q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenGapZeckendorf.fibWord_eq_zeckendorf_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The least-digit table has the same two-step Fibonacci concatenation as fibWord. The upper block follows from Zeckendorf uniqueness after prefixing index Q+3, and the cases Q=0 and Q=1 are computed from the canonical representations of zero and one.

**Theorem 1.2 (The frozen gap word is the least-digit test).**

$$\operatorname{goldenGapWord}\left(Q\right) = \operatorname{ofFn}\left(\operatorname{leastZeckendorfDigitTest}\left(Q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenGapZeckendorf.goldenGapWord_eq_zeckendorf_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This consequence rewrites only through the frozen golden_full_gap_word theorem, so the tower identification is a necessary proof dependency rather than a parallel derivation.

Deferred: the explicit Beatty form, with a large letter exactly when floor((i+2)/phi)-floor((i+1)/phi)=1, is not proved in this S0 node. Its next admissible step is an S1 bridge from absence of digit 2 to goldenMechanicalLetter(i+1)=1; S0 does not import S1.

## References

- Truth anchor: `D5/S0/Tower/GoldenGapZeckendorf.fibWord_eq_zeckendorf_word`
- Truth anchor: `D5/S0/Tower/GoldenGapZeckendorf.goldenGapWord_eq_zeckendorf_word`
- Dependency: [D5/S0/Conventions/WDigits](../Conventions/WDigits.md)
- Dependency: [D5/S0/Tower/GoldenGapWord](GoldenGapWord.md)
