# Integer HF Codes

## Abstract

Tagged natural magnitudes give an exact finite set representation of signed integers.

**Definition 1.1 (All signed integers have exactly the legal codes).**

Lean statement: `D5/S0/History/Spacetime/IntegerEncoding.int_code_equiv`

*Formalization.* `D5/S0/History/Spacetime/IntegerEncoding.int_code_equiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The structural grammar permits tag zero with any natural magnitude and tag one with a strictly positive magnitude. Natural codes use von Neumann ordinals. Negative zero is excluded, and case analysis on Int proves both round trips.

**Theorem 1.2 (Reconstruction preserves the literal code).**

Lean statement: `D5/S0/History/Spacetime/IntegerEncoding.encode_decodeInt`

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/IntegerEncoding.encode_decodeInt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every structurally legal code is recovered after decoding. This finite representation supplies the coordinate and time fields of archive records.

## References

- Truth anchor: `D5/S0/History/Spacetime/IntegerEncoding.encode_decodeInt`
- Truth anchor: `D5/S0/History/Spacetime/IntegerEncoding.int_code_equiv`
- Dependency: [D5/S0/History/Spacetime/HFEncoding](HFEncoding.md)
