# Mixed denominators in four-digit integer coverage

## Abstract

A restriction on mixing reduced denominators in dense integer coverage by four digits.

**Theorem 1.1 (Two and three cannot both occur as reduced denominators).**

$$\operatorname{FourDigitIntegerCoverage}\left(J, L\right) \land 4^{\operatorname{card}\left(J\right) - 1} < L \Rightarrow \operatorname{NoMixedHalfAndThirdWeights}\left(J\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubsetSpectrum/MixedDigitDenominators.no_mixed_denominators_of_capacity_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix real weights on a finite index set J. Every integer level from zero through L minus one is represented by a weighted sum with digits in zero through three. If L exceeds four to the power card J minus one, two distinct coordinates cannot have weights a divided by two and b divided by three with odd integer a and integer b indivisible by three.

For two representations that agree off those coordinates, subtract the level equations and clear denominators. Reduction modulo two recovers equality of the first digits' remainders modulo two. Reduction modulo three gives the corresponding equality for the second digits. Both quotients have at most two values. Thus the outside digits and the two quotients together encode each level injectively, using at most four to the power card J minus one codes.

## References

- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/MixedDigitDenominators.no_mixed_denominators_of_capacity_gap`
