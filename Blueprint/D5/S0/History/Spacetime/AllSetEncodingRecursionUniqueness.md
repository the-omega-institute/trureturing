# Uniqueness of Recursive Set Encoding

## Abstract

Uniqueness of Recursive Set Encoding.

**Theorem 1.1 (Uniqueness of the total recursive encoding).**

Lean statement: `D5/S0/History/Spacetime/AllSetEncodingRecursionUniqueness.enc_unique`

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/AllSetEncodingRecursionUniqueness.enc_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In any universe, every total function on sets satisfying the Zeckendorf encoding recursion equals Enc. On a finite ordinal, the function returns the natural leaf indexed by that ordinal. On every other set, it returns the ordered pair of tag one and the image of its members under the same function. Membership induction gives equality at every set: the natural branch is fixed, and equality on members determines the image in the other branch.

## References

- Truth anchor: `D5/S0/History/Spacetime/AllSetEncodingRecursionUniqueness.enc_unique`
- Dependency: [D5/S0/History/Spacetime/AllSetZeckendorfEncoding](AllSetZeckendorfEncoding.md)
