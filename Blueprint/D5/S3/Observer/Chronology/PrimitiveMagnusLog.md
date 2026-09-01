# Primitive Degree-Two Magnus Logarithm

## Abstract

Subtracting the tensor square of degree one extracts the primitive alternating Magnus coordinate.

**Definition 1.1 (Universal tensor bracket).**

Lean statement: `D5/S3/Observer/Chronology/PrimitiveMagnusLog.tensorLieBracket`

*Formalization.* `D5/S3/Observer/Chronology/PrimitiveMagnusLog.tensorLieBracket` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The alternating tensor of two vectors is their ordered pure tensor minus the reversed pure tensor.

**Definition 1.2 (Doubled primitive Magnus coordinate).**

Lean statement: `D5/S3/Observer/Chronology/PrimitiveMagnusLog.doubledPrimitiveMagnus`

*Formalization.* `D5/S3/Observer/Chronology/PrimitiveMagnusLog.doubledPrimitiveMagnus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The tensor square of degree one is removed from doubled degree two.

**Definition 1.3 (Alternating tensor condition).**

Lean statement: `D5/S3/Observer/Chronology/PrimitiveMagnusLog.IsAlternatingTensor`

*Formalization.* `D5/S3/Observer/Chronology/PrimitiveMagnusLog.IsAlternatingTensor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A degree-two tensor is alternating when tensor flip sends it to its additive inverse.

**Theorem 1.4 (Bracket orientation reversal).**

Lean statement: `D5/S3/Observer/Chronology/PrimitiveMagnusLog.tensor_lie_bracket_swap`

*Formalization.* `D5/S3/Observer/Chronology/PrimitiveMagnusLog.tensor_lie_bracket_swap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exchanging the two vector inputs negates the tensor bracket.

**Theorem 1.5 (Tensor flip negates the bracket).**

Lean statement: `D5/S3/Observer/Chronology/PrimitiveMagnusLog.tensor_flip_lie_bracket`

*Formalization.* `D5/S3/Observer/Chronology/PrimitiveMagnusLog.tensor_flip_lie_bracket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The universal bracket lies in the anti-invariant subspace of tensor flip.

**Theorem 1.6 (Tensor BCH law).**

Lean statement: `D5/S3/Observer/Chronology/PrimitiveMagnusLog.doubled_primitive_magnus_mul`

*Formalization.* `D5/S3/Observer/Chronology/PrimitiveMagnusLog.doubled_primitive_magnus_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The logarithm of a Chen product is the sum of the two logarithms plus the cross bracket.

**Theorem 1.7 (Group-like implies primitive alternating).**

Lean statement: `D5/S3/Observer/Chronology/PrimitiveMagnusLog.doubled_primitive_magnus_alternating`

*Formalization.* `D5/S3/Observer/Chronology/PrimitiveMagnusLog.doubled_primitive_magnus_alternating` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite group-like equation forces the doubled Magnus coordinate to be anti-invariant under tensor flip.

**Theorem 1.8 (Two events give their bracket).**

Lean statement: `D5/S3/Observer/Chronology/PrimitiveMagnusLog.doubled_primitive_magnus_two_events`

*Formalization.* `D5/S3/Observer/Chronology/PrimitiveMagnusLog.doubled_primitive_magnus_two_events` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The primitive logarithm of a two-event chronology is exactly the tensor Lie bracket.

**Theorem 1.9 (Chronological tensor BCH append law).**

Lean statement: `D5/S3/Observer/Chronology/PrimitiveMagnusLog.doubled_primitive_magnus_append`

*Formalization.* `D5/S3/Observer/Chronology/PrimitiveMagnusLog.doubled_primitive_magnus_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Word concatenation transports Chen multiplication to the degree-two tensor BCH formula.

**Theorem 1.10 (Every word logarithm is alternating).**

Lean statement: `D5/S3/Observer/Chronology/PrimitiveMagnusLog.chronological_primitive_magnus_alternating`

*Formalization.* `D5/S3/Observer/Chronology/PrimitiveMagnusLog.chronological_primitive_magnus_alternating` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite chronological tensor signature has a primitive anti-invariant degree-two logarithm.

## References

- Truth anchor: `D5/S3/Observer/Chronology/PrimitiveMagnusLog.tensorLieBracket`
- Truth anchor: `D5/S3/Observer/Chronology/PrimitiveMagnusLog.doubledPrimitiveMagnus`
- Truth anchor: `D5/S3/Observer/Chronology/PrimitiveMagnusLog.IsAlternatingTensor`
- Truth anchor: `D5/S3/Observer/Chronology/PrimitiveMagnusLog.tensor_lie_bracket_swap`
- Truth anchor: `D5/S3/Observer/Chronology/PrimitiveMagnusLog.tensor_flip_lie_bracket`
- Truth anchor: `D5/S3/Observer/Chronology/PrimitiveMagnusLog.doubled_primitive_magnus_mul`
- Truth anchor: `D5/S3/Observer/Chronology/PrimitiveMagnusLog.doubled_primitive_magnus_alternating`
- Truth anchor: `D5/S3/Observer/Chronology/PrimitiveMagnusLog.doubled_primitive_magnus_two_events`
- Truth anchor: `D5/S3/Observer/Chronology/PrimitiveMagnusLog.doubled_primitive_magnus_append`
- Truth anchor: `D5/S3/Observer/Chronology/PrimitiveMagnusLog.chronological_primitive_magnus_alternating`
- Dependency: [D5/S3/Observer/Chronology/TruncatedTensorHopf](TruncatedTensorHopf.md)
