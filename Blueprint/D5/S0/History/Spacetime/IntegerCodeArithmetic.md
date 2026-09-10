# Arithmetic and Order on Integer HF Codes

## Abstract

The frozen signed-magnitude HF integer encoding carries the transported ordered ring arithmetic.

**Definition 1.1 (Integer arithmetic on the literal codes).**

Lean statement: `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_ring_equiv`

*Formalization.* `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_ring_equiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mathlib Equiv.commRing and Equiv.ringEquiv transport the integer ring to exactly the structural signed-magnitude HF subtype. The forward function is the frozen decodeInt, and the inverse is the frozen int_code_equiv encoder.

**Definition 1.2 (Integer order through the same functions).**

Lean statement: `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_order_iso`

*Formalization.* `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_order_iso` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mathlib Equiv.linearOrder transports order and maximum through the same frozen equivalence. The OrderIso has the same decoder and encoder as the RingEquiv; it introduces no alternative coding.

**Theorem 1.3 (Encoding zero).**

Lean statement: `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_zero`

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original integer encoder sends zero to the zero of the transported code ring.

**Theorem 1.4 (Decoding zero).**

Lean statement: `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_zero`

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original decoder sends the zero code of the transported ring to integer zero.

**Theorem 1.5 (Encoding one).**

Lean statement: `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_one`

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original integer encoder sends one to the unit of the transported code ring.

**Theorem 1.6 (Decoding one).**

Lean statement: `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_one`

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original decoder sends the unit code of the transported ring to integer one.

**Theorem 1.7 (Encoding addition).**

Lean statement: `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_add`

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all integers, encoding their sum equals the sum of their literal HF codes. This is an application of the inverse RingEquiv addition law.

**Theorem 1.8 (Decoding addition).**

Lean statement: `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_add`

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all legal integer codes, the original decoder of their code-ring sum equals the sum of their decoded integers.

**Theorem 1.9 (Encoding multiplication).**

Lean statement: `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_mul`

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all integers, encoding their product equals the product of their codes in the transported ring.

**Theorem 1.10 (Decoding multiplication).**

Lean statement: `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_mul`

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all legal codes, decoding the transported product equals multiplying the decoded integers.

**Theorem 1.11 (Encoding negation).**

Lean statement: `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_neg`

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer, its encoded negative is the additive inverse of its code.

**Theorem 1.12 (Decoding negation).**

Lean statement: `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_neg`

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every legal code, decoding its additive inverse gives the negative of its decoded integer.

**Theorem 1.13 (Encoding subtraction).**

Lean statement: `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_sub`

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all integers, the original encoder preserves subtraction in the transported code ring.

**Theorem 1.14 (Decoding subtraction).**

Lean statement: `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_sub`

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all legal codes, the original decoder preserves subtraction into ordinary integers.

**Theorem 1.15 (Encoding non-strict order).**

Lean statement: `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_le`

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all integers, comparison of their codes is equivalent to comparison of the original integers. The inverse OrderIso supplies both directions.

**Theorem 1.16 (Decoding non-strict order).**

Lean statement: `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_le`

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all legal codes, comparison of the decoded integers is equivalent to comparison in the transported code order.

**Theorem 1.17 (Encoding strict order).**

Lean statement: `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_lt`

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all integers, strict comparison of their codes is equivalent to strict comparison of the original integers.

**Theorem 1.18 (Decoding strict order).**

Lean statement: `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_lt`

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all legal codes, strict comparison of the decoded integers is equivalent to strict comparison in the code order.

**Theorem 1.19 (Encoding maximum).**

Lean statement: `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_max`

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_max` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all integers, encoding their maximum gives the maximum of their codes. This follows from monotonicity of the inverse OrderIso.

**Theorem 1.20 (Decoding maximum).**

Lean statement: `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_max`

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_max` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all legal codes, decoding their maximum gives the maximum of their decoded integers.

**Theorem 1.21 (Order and ring arithmetic are compatible).**

Lean statement: `D5/S0/History/Spacetime/IntegerCodeArithmetic.instIsStrictOrderedRing`

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/IntegerCodeArithmetic.instIsStrictOrderedRing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's generic ordered-ring pullback consumes the proved decoding laws for zero, one, addition, multiplication and both comparisons. It supplies the ordered-ring instance on the same subtype without assuming compatibility as a new field.

**Theorem 1.22 (Encoding the generated-event time expression).**

Lean statement: `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_max_add_one`

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_max_add_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The universal addition, maximum and unit laws prove that encoding maximum parent time plus one equals maximum encoded parent time plus one.

**Theorem 1.23 (Decoding the generated-event time expression).**

Lean statement: `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_max_add_one`

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_max_add_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Decoding maximum code parent time plus one gives the maximum of the original decoded times plus one. These are arithmetic representation laws; internal ZFC ContextGraph and OperationGraph realization obligations remain for later work.

## References

- Truth anchor: `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_add`
- Truth anchor: `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_le`
- Truth anchor: `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_lt`
- Truth anchor: `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_max`
- Truth anchor: `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_max_add_one`
- Truth anchor: `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_mul`
- Truth anchor: `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_neg`
- Truth anchor: `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_one`
- Truth anchor: `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_order_iso`
- Truth anchor: `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_ring_equiv`
- Truth anchor: `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_sub`
- Truth anchor: `D5/S0/History/Spacetime/IntegerCodeArithmetic.decode_zero`
- Truth anchor: `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_add`
- Truth anchor: `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_le`
- Truth anchor: `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_lt`
- Truth anchor: `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_max`
- Truth anchor: `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_max_add_one`
- Truth anchor: `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_mul`
- Truth anchor: `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_neg`
- Truth anchor: `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_one`
- Truth anchor: `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_sub`
- Truth anchor: `D5/S0/History/Spacetime/IntegerCodeArithmetic.encode_zero`
- Truth anchor: `D5/S0/History/Spacetime/IntegerCodeArithmetic.instIsStrictOrderedRing`
- Dependency: [D5/S0/History/Spacetime/IntegerEncoding](IntegerEncoding.md)
