# Fixed-length positive power sums

## Abstract

For each exponent at least two, a fixed positive length represents every sufficiently large natural number.

**Definition 1.1 (Exactly j positive powers).**

Lean statement: `D5/S3/Arith/Additive/BenfieldLippard/PositiveFixedLength.PosRep`

*Formalization.* `D5/S3/Arith/Additive/BenfieldLippard/PositiveFixedLength.PosRep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* The Waring formalization authors (2026). *Waring's theorem in Lean 4*. URL: <https://github.com/yunyougu50-create/waring-lean4/tree/cd0735c253f3b640262fcc74a61306cb41e23765>.

*Commentary.*

A representation has one positive natural base at each index of Fin j, and the sum of the kth powers is n.

**Theorem 1.2 (A fixed positive length).**

Lean statement: `D5/S3/Arith/Additive/BenfieldLippard/PositiveFixedLength.eventual_fixed_length`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/BenfieldLippard/PositiveFixedLength.eventual_fixed_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Waring formalization authors (2026). *Waring's theorem in Lean 4*. URL: <https://github.com/yunyougu50-create/waring-lean4/tree/cd0735c253f3b640262fcc74a61306cb41e23765>.

*Commentary.*

Let g be the uniform Waring bound for the exponent k. Put a = 2^k − 1, m = a^(k−1), and R = m·2^k. A block of m twos and a block consisting of a followed by m ones both contribute R, and their lengths differ by one.

Apply the Waring bound after reserving g copies of R and one extra one. If i positive bases survive removal of zeros, append i short blocks, g−i long blocks and the extra one. This gives a representation of length g(m+1)+1, independent of the target.

## References

- Truth anchor: `D5/S3/Arith/Additive/BenfieldLippard/PositiveFixedLength.PosRep`
- Truth anchor: `D5/S3/Arith/Additive/BenfieldLippard/PositiveFixedLength.eventual_fixed_length`
- Dependency: [D5/S3/Arith/Additive/Waring/WaringTheorem2](../Waring/WaringTheorem2.md)
