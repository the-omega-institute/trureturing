# A finite matrix packet for the binary icosahedral obstruction

## Abstract

Explicit matrices for the SL2(F5) center-lift packet

Work in the determinant-one two by two matrices over ZMod 5. The displayed generators are u = [[0,1],[4,1]] and v = [[1,1],[0,1]]. Define lowReturn = v^{-1}u^2, highReturn = v^2u, and centralReturn = vu^3.

**Theorem 1.1 (The explicit return-word identities).**

Lean statement: `D5/S3/Geometry/Hyperideal/SL2F5ExplicitPacket.sl2_five_explicit_relations`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/SL2F5ExplicitPacket.sl2_five_explicit_relations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite calculation gives lowReturn^2 = -I, lowReturn^4 = I, and lowReturn != I. It also gives highReturn^3 = I and highReturn != I, so the two displayed return words have orders four and three respectively.

The same computation verifies u^3 = -I, v^5 = I, u v = lowReturn, centralReturn = -v, and centralReturn^5 = -I. These are exact identities for the supplied matrices over ZMod 5.

The packet supplies the explicit finite center-lift data used in CFMP section 124. It does not assert a geometric realization, a general covering theorem, or a new identification of the binary icosahedral group. The faithful source-bound escape audit remains unfinished under https://github.com/the-omega-institute/trureturing/issues/19034.

**Theorem 1.2 (The exact finite group cardinality).**

Lean statement: `D5/S3/Geometry/Hyperideal/SL2F5ExplicitPacket.sl2_five_cardinality`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/SL2F5ExplicitPacket.sl2_five_cardinality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant-one matrix group over ZMod 5 has exactly 120 elements, verified by finite computation in the kernel.

This cardinality is used only as a finite size fact for the explicit packet. It does not by itself supply the group-generation argument or the geometric existence input from the surrounding theory.

The faithful source-bound escape audit remains unfinished under https://github.com/the-omega-institute/trureturing/issues/19034.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/SL2F5ExplicitPacket.sl2_five_cardinality`
- Truth anchor: `D5/S3/Geometry/Hyperideal/SL2F5ExplicitPacket.sl2_five_explicit_relations`
