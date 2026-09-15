# All-Set Zeckendorf Encoding

## Abstract

All-Set Zeckendorf Encoding.

**Theorem 1.1 (Injectivity and decoding).**

Lean statement: `D5/S0/History/Spacetime/AllSetZeckendorfEncoding.enc_injective_and_left_inverse`

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/AllSetZeckendorfEncoding.enc_injective_and_left_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In any universe, encode a finite von Neumann ordinal by tag zero paired with its finite Zeckendorf digit graph. Encode every other set by tag one paired with the set of encodings of its members. Membership recursion defines this map on all sets. Two encodings are equal if and only if their original sets are equal, and decoding the valid code of any set recovers that set. The natural number zero has an empty digit graph; positive words retain all positions, including their zero digits.

## References

- Truth anchor: `D5/S0/History/Spacetime/AllSetZeckendorfEncoding.enc_injective_and_left_inverse`
